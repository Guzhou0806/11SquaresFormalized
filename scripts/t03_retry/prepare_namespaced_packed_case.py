"""Copy exact declaration bodies into bounded modules; preserve public types and all data."""
from pathlib import Path
from packed_namespace_transform import Renamer
import argparse, ast, ctypes, datetime, hashlib, json, os, re, sys, zipfile
ap=argparse.ArgumentParser();ap.add_argument('--case',type=int,required=True);ap.add_argument('--revision',type=int,default=0);ap.add_argument('--canonical',action='store_true');ap.add_argument('--coordinate-refl',action='store_true');ap.add_argument('--all-equality-refl',action='store_true');ap.add_argument('--plan');ap.add_argument('--kit',required=True);ap.add_argument('--transport-dir');ap.add_argument('--scratch-root',type=Path,required=True);ap.add_argument('--source-root',type=Path)
args=ap.parse_args();case=args.case
from retry_paths import kit_paths,low_priority_single_core,metadata_path
K,E,transport_root=kit_paths(args.kit,args.transport_dir);S=args.source_root.resolve() if args.source_root else K/'eleven-square-lean';scratch=args.scratch_root.resolve();assert S.is_dir() and scratch.is_dir()
low_priority_single_core()
if args.all_equality_refl:args.coordinate_refl=True
assert case in {r['case'] for r in json.loads((E/'forward-workload-inventory.json').read_text())['records']}
plan_name=args.plan or f'case{case}-packed-compilation-plan.json'
assert Path(plan_name).name==plan_name and plan_name.startswith(f'case{case}-packed-compilation') and plan_name.endswith('-plan.json')
plan=json.loads((E/plan_name).read_text());assert plan['case']==case
assert plan['status']=='EXACT_SOURCE_GROUPING_PLAN_NOT_LEAN_CHECKED'
revision=args.revision;assert revision in [0,1]
revision_tag='' if revision==0 else f'-retry{revision:02d}'
record=E/f'case{case}-packed-namespaced{revision_tag}-publication.json';assert not record.exists()
archive=metadata_path(plan['source_archive'])
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        while block:=f.read(1024*1024):h.update(block)
    return h.hexdigest()
assert sha(archive)==plan['source_archive_sha256']
tactic=S/'ElevenSquare/Tasks/T03/KernelBoolRefl.lean'
assert sha(tactic)=='90111f1782484d93843ab7e8ec6789744ebf90afdd8deb6fa2d3ddf3880513ce'
equality_helper=S/'ElevenSquare/Tasks/T03/KernelEqualityRefl.lean'
if args.coordinate_refl:
    equality_pilot=json.loads((E/'equality-refl-benchmark.json').read_text())
    assert equality_pilot['status']=='IDENTICAL_COORDINATE_EQUALITY_COMPARISON_PASSED' and equality_pilot['measured_gain'] and equality_pilot['kernel_negative_control_rejected']
    benchmark_ast=ast.parse((E/'benchmark_equality_refl.py').read_text(encoding='utf8'))
    tested_helper=next(n.value.value for n in benchmark_ast.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='helper' for t in n.targets))
    assert tested_helper in equality_helper.read_text(encoding='utf8')
    retained_pilot=json.loads((E/'case1311-coordinate-binding-lean-repair-probe-v3.json').read_text())
    assert retained_pilot['status']=='ALL_EIGHT_EXACT_FAILED_BINDINGS_ACCEPTED_BY_LEAN'
    assert all(c['exit_code']==0 for c in retained_pilot['checks'])
module_tag='PackedNamespaced' if revision==0 else f'PackedNamespacedRetry{revision:02d}'
plan['chunk_imports']={k.replace('.Packed.','.'+module_tag+'.'):[m.replace('.Packed.','.'+module_tag+'.') for m in v] for k,v in plan['chunk_imports'].items()}
plan['root_module']=plan['root_module'].replace('.Packed.','.'+module_tag+'.')
new_task=f'forward-case{case}-packed-namespaced{revision_tag}-retry-assembly-task.json'
if args.canonical:new_task=f'forward-case{case}-assembly-task.json'
prepared=E/('.prepared-'+new_task);assert not prepared.exists() and (args.canonical or not (E/new_task).exists())
task=dict(plan['original_task']);task['modules']=[plan['root_module']]
task_raw=(json.dumps(task,indent=2)+'\n').encode()
target=transport_root/(f'.t03-packed-case{case}-ready.zip' if args.canonical else '.t03-runtime-sync-'+Path(new_task).stem+'.zip');assert not target.exists()
temporary=scratch/(f'case{case}-packed-namespaced-transport-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'.zip')
assert not temporary.exists()
chunks={};bindings=[];finite_checks=0;coordinate_equalities=0;remaining_equalities=0
with zipfile.ZipFile(archive) as source:
    manifest=json.loads(source.read('source-sync-manifest.json'))
    def sources():
        for group in plan['groups']:
            for m in group:
                name='project/'+m.replace('.','/')+'.lean';raw=source.read(name)
                assert hashlib.sha256(raw).hexdigest()==manifest[name]==plan['source_hashes'][m]
                yield m,raw.decode().replace('\r\n','\n')
    renamer=Renamer(sources,suffix=f'PackedCase{case}')
    print(json.dumps(dict(status='PRIVATE_DECLARATION_MAP_READY',declarations=len(renamer.declarations),namespaces=len(renamer.namespaces))),flush=True)
    target_name=task['axiom_targets'][0]
    assert task['axiom_targets']==[target_name] and target_name.endswith('.certificate_exists')
    target_namespace=target_name.rsplit('.',1)[0]
    certificate_module=plan['original_task']['modules'][0]
    certificate_text=source.read('project/'+certificate_module.replace('.','/')+'.lean').decode().replace('\r\n','\n')
    header=re.search(r'(theorem certificate_exists\s*:[\s\S]*?)\s*:=',certificate_text)[1]
    renamed_target=renamer.resolve(target_name,'')
    assert renamed_target!=target_name
    bridge='\nnamespace '+target_namespace+'\nnoncomputable section\n'+header+' := by\n  exact _root_.'+renamed_target+'\nend\nend '+target_namespace+'\n'
    for i,group in enumerate(plan['groups']):
        module=next(m for m in plan['chunk_imports'] if m.endswith(f'.Chunk{i:03d}'))
        parts=['\n'.join('import '+m for m in plan['chunk_imports'][module])+'\n\n'];group_equalities=0
        for original_module in group:
            name='project/'+original_module.replace('.','/')+'.lean'
            raw=source.read(name);assert hashlib.sha256(raw).hexdigest()==manifest[name]==plan['source_hashes'][original_module]
            text=raw.decode().replace('\r\n','\n')
            body=re.sub(r'^import [^\n]*\n','',text,flags=re.M)
            renamed=renamer.transform(body)
            assert re.findall(r'\b[0-9]+\b',body)==re.findall(r'\b[0-9]+\b',renamed),('Numeric data changed',original_module)
            body=renamed
            # Exact Bool.equal-true claims keep their statements and computation; only the ordinary refl construction changes.
            body,n=re.subn(r'= true := by rfl\b','= true := by t03_bool_refl',body);finite_checks+=n
            if re.search(r'UniversalCollision[0-9a-f]{24}Coarsened$',original_module):
                n=body.count('checked := by rfl');finite_checks+=n;body=body.replace('checked := by rfl','checked := by t03_bool_refl')
            if args.coordinate_refl:
                body,n=re.subn(r'^theorem hom_binding : homVertices.map HomPoint.point = vertices := by rfl$',
                    'theorem hom_binding : homVertices.map HomPoint.point = vertices := by t03_eq_refl',body,flags=re.M)
                coordinate_equalities+=n;group_equalities+=n
                body,n=re.subn(r'^theorem homRetained_binding : homRetained.map HomPoint.point = retained := by rfl$',
                    'theorem homRetained_binding : homRetained.map HomPoint.point = retained := by t03_eq_refl',body,flags=re.M)
                coordinate_equalities+=n;group_equalities+=n
            if args.all_equality_refl:
                # Keep every statement and numeric token. Construct ordinary
                # Eq.refl once for all remaining generated equality proofs;
                # the original kernel still checks each resulting declaration.
                body,n=re.subn(r'(?<=by )rfl\b|(?<=<;> )rfl\b','t03_eq_refl',body)
                remaining_equalities+=n;group_equalities+=n
                assert re.findall(r'\b[0-9]+\b',renamed)==re.findall(r'\b[0-9]+\b',body)
            parts.append('-- Original source: '+original_module+'; SHA256 '+manifest[name]+'\nsection\n'+body+'\nend\n\n')
            bindings.append(dict(module=original_module,source_sha256=manifest[name],group=module))
        if group_equalities:
            parts.insert(0,'import ElevenSquare.Tasks.T03.KernelEqualityRefl\n')
            plan['chunk_imports'][module].append('ElevenSquare.Tasks.T03.KernelEqualityRefl')
        if module==plan['root_module']:parts.append(bridge)
        raw=''.join(parts).encode();assert len(raw)<16*1024*1024
        name='project/'+module.replace('.','/')+'.lean';path=S/name[8:]
        assert not path.exists();path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
        chunks[name]=dict(path=str(path),sha256=hashlib.sha256(raw).hexdigest())
    selected=set();visiting=set()
    def visit(module):
        if module in selected:return
        assert module not in visiting;visiting.add(module)
        name='project/'+module.replace('.','/')+'.lean'
        if name in chunks:deps=plan['chunk_imports'][module]
        elif module in ['ElevenSquare.Tasks.T03.KernelBoolRefl','ElevenSquare.Tasks.T03.KernelEqualityRefl']:deps=[]
        else:deps=plan['graph'][module]
        for dep in deps:
            if dep=='ElevenSquare' or dep.startswith('ElevenSquare.'):visit(dep)
        visiting.remove(module);selected.add(module)
    visit(plan['root_module'])
    assert {n[8:-5].replace('/','.') for n in chunks}<=selected
    entries={'project/'+m.replace('.','/')+'.lean' for m in selected}
    entries.update('project/'+r for r in ['lakefile.lean','lake-manifest.json','lean-toolchain','scripts/lake.sh',
                   'scripts/check_handoff.py','scripts/lean_small_check.py','verification/LOW_RESOURCE_MODE.json'])
    entries.add('TASK.json');new_manifest={}
    with zipfile.ZipFile(temporary,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=1) as output:
        for name in sorted(entries):
            if name in chunks:
                raw=Path(chunks[name]['path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==chunks[name]['sha256']
            elif name=='project/ElevenSquare/Tasks/T03/KernelBoolRefl.lean':raw=tactic.read_bytes()
            elif name=='project/ElevenSquare/Tasks/T03/KernelEqualityRefl.lean':raw=equality_helper.read_bytes()
            else:raw=source.read(name);assert hashlib.sha256(raw).hexdigest()==manifest[name],name
            if name.endswith('.lean'):assert len(raw)<16*1024*1024
            new_manifest[name]=hashlib.sha256(raw).hexdigest();output.writestr(name,raw)
        new_manifest[new_task]=hashlib.sha256(task_raw).hexdigest();output.writestr(new_task,task_raw)
        output.writestr('source-sync-manifest.json',json.dumps(new_manifest))
with zipfile.ZipFile(temporary) as check:
    assert len(check.namelist())==len(set(check.namelist()))
    assert json.loads(check.read('source-sync-manifest.json'))==new_manifest
    for name,expected in new_manifest.items():assert hashlib.sha256(check.read(name)).hexdigest()==expected,name
assert sha(archive)==plan['source_archive_sha256']
with temporary.open('rb') as src,target.open('xb') as dst:
    while block:=src.read(1024*1024):dst.write(block)
assert sha(target)==sha(temporary)
prepared.write_bytes(task_raw)
payload=dict(status='PACKED_CASE_PREPARED_NOT_LEAN_CHECKED_OR_DISPATCHED',case=case,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
             original_archive_sha256=plan['source_archive_sha256'],archive=str(target),archive_sha256=sha(target),task=new_task,
             root_module=plan['root_module'],axiom_targets=task['axiom_targets'],groups=len(chunks),original_modules_grouped=len(bindings),
             finite_bool_proof_constructions_changed=finite_checks,original_sources_and_data_unchanged=True,
             packed_body_bindings=bindings,source_manifest=new_manifest,large_temporary_archive=str(temporary),
             prepared_task=str(prepared),full_case_and_final_target_audits_pending=True,lean_processes_started=0)
payload.update(private_namespaces_renamed=True,renamed_declarations=len(renamer.declarations),renamed_namespaces=len(renamer.namespaces),
               renamed_references=renamer.changed_references,namespace_roots=sorted(renamer.roots),
               namespace_suffix=renamer.suffix,exact_certificate_header=header,
               exact_certificate_header_sha256=hashlib.sha256(header.encode()).hexdigest(),
               exact_original_target_bridge=bridge,numeric_tokens_unchanged=True,canonical_task_publication=args.canonical)
payload.update(coordinate_equality_refl_enabled=args.coordinate_refl,coordinate_equality_proof_constructions_changed=coordinate_equalities)
payload.update(all_remaining_equality_refl_enabled=args.all_equality_refl,
               remaining_equality_proof_constructions_changed=remaining_equalities,
               every_changed_proof_requires_original_kernel_check=True)
payload.update(group_module_prefix=plan['root_module'].rsplit('.',1)[0]+'.',source_plan=plan_name)
record.write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps({k:v for k,v in payload.items() if k not in ['packed_body_bindings','source_manifest','namespace_roots']}),flush=True)
