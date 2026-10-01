"""Apply a hash-bound pending source supplement into a fresh source directory.

No Lean process is started. The unchanged original checker must verify proofs.
"""
from pathlib import Path, PurePosixPath
from contextlib import ExitStack
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

def apply_supplement(base,supplement,supplement_sha256,output,prior_supplements=()):
    if output.exists():raise ValueError('Output directory must be fresh')
    if file_sha(supplement)!=supplement_sha256:raise ValueError('Supplement digest mismatch')
    with ExitStack() as stack:
        overlay=stack.enter_context(zipfile.ZipFile(supplement))
        original=stack.enter_context(zipfile.ZipFile(base))
        safe_members(overlay);bi=safe_members(original)
        recipe=json.loads(overlay.read('SUPPLEMENT-RECIPE.json'))
        if recipe['format']!='T03-pending-single-module-supplement-v1':raise ValueError('Unsupported recipe')
        if recipe['full_case_audit_accepted']:raise ValueError('Pending source recipe has an inconsistent acceptance claim')
        if file_sha(base)!=recipe['required_base_zip_sha256']:raise ValueError('Base ZIP digest mismatch')
        required=recipe.get('required_prior_supplements',[])
        if len(required)!=len(prior_supplements) or len(required)>99:raise ValueError('Prior supplement chain differs')
        layers=[];inputs=[(supplement,supplement_sha256)];expected_chain=[]
        for path,entry in zip(prior_supplements,required):
            digest=entry['asset_sha256']
            if file_sha(path)!=digest:raise ValueError('Prior supplement digest mismatch')
            z=stack.enter_context(zipfile.ZipFile(path));layers.append(z);inputs.append((path,digest));expected_chain.append(digest)
        layers.append(overlay)
        current=json.loads(original.read('source-sync-manifest.json'))
        if set(bi)!=set(current)|{'source-sync-manifest.json'}:raise ValueError('Base manifest member set differs')
        replacements={};changed_lean=set()
        for index,z in enumerate(layers):
            oi=safe_members(z);r=json.loads(z.read('SUPPLEMENT-RECIPE.json'));names=set(r['overlay_members'])
            if r['format']!=recipe['format'] or r['full_case_audit_accepted'] or r['required_base_zip_sha256']!=recipe['required_base_zip_sha256']:raise ValueError('Inconsistent source layer')
            if r.get('case')!=recipe.get('case'):raise ValueError('Source layer case differs')
            if [v['asset_sha256'] for v in r.get('required_prior_supplements',[])]!=expected_chain[:index]:raise ValueError('Source layer predecessor chain differs')
            if set(oi)!=names|{'SUPPLEMENT-RECIPE.json'} or not names<=set(bi):raise ValueError('Overlay member set differs')
            new=json.loads(z.read('source-sync-manifest.json'))
            if set(new)!=set(current):raise ValueError('Manifest member set differs')
            source=r['changed_source_member']
            if current[source]!=r['old_source_sha256'] or new[source]!=r['new_source_sha256']:raise ValueError('Changed source binding differs')
            if {n for n in current if current[n]!=new[n]}!=names-{'source-sync-manifest.json'}:raise ValueError('Unexpected manifest changes')
            if {n for n in names if n.endswith('.lean')}!={source}:raise ValueError('Each supplement must change exactly one Lean module')
            for n in names:
                if n.endswith('.lean') and z.getinfo(n).file_size>16*1024*1024:raise ValueError('Lean source exceeds16MiB')
                raw=z.read(n);digest=r['overlay_members'][n]['sha256']
                if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('Overlay member digest differs')
                replacements[n]=(z,digest)
            changed_lean.add(source);current=new
        scratch=output.with_name(output.name+'.applying-'+uuid.uuid4().hex)
        if scratch.resolve().parent!=output.resolve().parent:raise ValueError('Unsafe fresh output directory')
        scratch.mkdir(parents=False)
        for n in sorted(bi):
            target=scratch/n
            if not target.resolve().is_relative_to(scratch.resolve()):raise ValueError('Unsafe output path')
            target.parent.mkdir(parents=True,exist_ok=True)
            z=replacements[n][0] if n in replacements else original
            if n.endswith('.lean') and z.getinfo(n).file_size>16*1024*1024:raise ValueError('Lean source exceeds16MiB')
            h=hashlib.sha256()
            with z.open(n) as f,target.open('xb') as out:
                for b in iter(lambda:f.read(1024*1024),b''):h.update(b);out.write(b)
            expected=replacements[n][1] if n in replacements else current[n]
            if h.hexdigest()!=expected or file_sha(target)!=expected:raise ValueError('Applied source member differs')
        if file_sha(base)!=recipe['required_base_zip_sha256'] or any(file_sha(p)!=d for p,d in inputs):raise ValueError('Input archive changed during application')
        os.rename(scratch,output)
    return dict(status='SOURCE_SUPPLEMENT_APPLIED_FULL_CASE_TARGET_AUDIT_PENDING',files=len(bi),changed_Lean_modules=len(changed_lean),source_layers=len(layers),Lean_processes_started=0)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--base',type=Path,required=True)
    p.add_argument('--supplement',type=Path,required=True)
    p.add_argument('--supplement-sha256',required=True)
    p.add_argument('--prior-supplement',type=Path,action='append',default=[],help='Ordered predecessor ZIPs required by the current recipe')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    from retry_paths import low_priority_single_core
    low_priority_single_core()
    print(json.dumps(apply_supplement(a.base.resolve(),a.supplement.resolve(),a.supplement_sha256,a.output.resolve(),[v.resolve() for v in a.prior_supplement])))

if __name__=='__main__':main()
