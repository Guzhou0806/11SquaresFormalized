"""Apply a hash-bound pending source supplement into a fresh source directory.

No Lean process is started. The unchanged original checker must verify proofs.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat, uuid, zipfile

def file_sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

def safe_members(z):
    result={}
    for i in z.infolist():
        p=PurePosixPath(i.filename)
        if p.is_absolute() or '..' in p.parts or ':' in i.filename or '\\' in i.filename:
            raise ValueError('Unsafe archive member')
        if i.is_dir() or stat.S_IFMT(i.external_attr>>16)==stat.S_IFLNK or i.flag_bits&1:
            raise ValueError('Directories, links and encrypted members are unsupported')
        if i.filename in result:raise ValueError('Duplicate archive member')
        result[i.filename]=i
    return result

def apply_supplement(base,supplement,supplement_sha256,output):
    if output.exists():raise ValueError('Output directory must be fresh')
    if file_sha(supplement)!=supplement_sha256:raise ValueError('Supplement digest mismatch')
    with zipfile.ZipFile(supplement) as overlay,zipfile.ZipFile(base) as original:
        oi=safe_members(overlay);bi=safe_members(original)
        recipe=json.loads(overlay.read('SUPPLEMENT-RECIPE.json'))
        if recipe['format']!='T03-pending-single-module-supplement-v1':raise ValueError('Unsupported recipe')
        if recipe['full_case_audit_accepted']:raise ValueError('Pending source recipe has an inconsistent acceptance claim')
        if file_sha(base)!=recipe['required_base_zip_sha256']:raise ValueError('Base ZIP digest mismatch')
        names=set(recipe['overlay_members'])
        if set(oi)!=names|{'SUPPLEMENT-RECIPE.json'} or not names<=set(bi):raise ValueError('Overlay member set differs')
        old=json.loads(original.read('source-sync-manifest.json'))
        new=json.loads(overlay.read('source-sync-manifest.json'))
        if set(bi)!=set(old)|{'source-sync-manifest.json'} or set(new)!=set(old):raise ValueError('Manifest member set differs')
        for n in names:
            raw=overlay.read(n)
            if hashlib.sha256(raw).hexdigest()!=recipe['overlay_members'][n]['sha256']:raise ValueError('Overlay member digest differs')
        source=recipe['changed_source_member']
        if old[source]!=recipe['old_source_sha256'] or new[source]!=recipe['new_source_sha256']:raise ValueError('Changed source binding differs')
        if {n for n in old if old[n]!=new[n]}!=names-{'source-sync-manifest.json'}:raise ValueError('Unexpected manifest changes')
        changed_lean={n for n in names if n.endswith('.lean')}
        if changed_lean!={source}:raise ValueError('Supplement must change exactly one Lean module')
        scratch=output.with_name(output.name+'.applying-'+uuid.uuid4().hex)
        scratch.mkdir(parents=False)
        for n in sorted(bi):
            target=scratch/n
            if not target.resolve().is_relative_to(scratch.resolve()):raise ValueError('Unsafe output path')
            target.parent.mkdir(parents=True,exist_ok=True)
            z=overlay if n in names else original
            if n.endswith('.lean') and z.getinfo(n).file_size>16*1024*1024:raise ValueError('Lean source exceeds16MiB')
            h=hashlib.sha256()
            with z.open(n) as f,target.open('xb') as out:
                for b in iter(lambda:f.read(1024*1024),b''):h.update(b);out.write(b)
            expected=recipe['overlay_members'][n]['sha256'] if n in names else old[n]
            if h.hexdigest()!=expected or file_sha(target)!=expected:raise ValueError('Applied source member differs')
        if file_sha(base)!=recipe['required_base_zip_sha256'] or file_sha(supplement)!=supplement_sha256:raise ValueError('Input archive changed during application')
        os.rename(scratch,output)
    return dict(status='SOURCE_SUPPLEMENT_APPLIED_FULL_CASE_TARGET_AUDIT_PENDING',files=len(bi),changed_Lean_modules=1,Lean_processes_started=0)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--base',type=Path,required=True)
    p.add_argument('--supplement',type=Path,required=True)
    p.add_argument('--supplement-sha256',required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    from retry_paths import low_priority_single_core
    low_priority_single_core()
    print(json.dumps(apply_supplement(a.base.resolve(),a.supplement.resolve(),a.supplement_sha256,a.output.resolve())))

if __name__=='__main__':main()
