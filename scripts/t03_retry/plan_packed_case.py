"""Plan source grouping from genuine existing receipts; start no Lean process."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, zipfile
ap=argparse.ArgumentParser();ap.add_argument('--case',type=int,required=True)
ap.add_argument('--source-archive');ap.add_argument('--expected-source-sha256');ap.add_argument('--record')
ap.add_argument('--kit',required=True);ap.add_argument('--runtime-root',required=True);ap.add_argument('--transport-dir');ap.add_argument('--scratch-root',required=True)
args=ap.parse_args();case=args.case
from retry_paths import kit_paths,low_priority_single_core
from pool_helpers import build_helpers
K,E,transport_root=kit_paths(args.kit,args.transport_dir);B=Path(args.runtime_root).resolve();scratch=Path(args.scratch_root).resolve()
assert B.is_dir() and scratch.is_dir()
assert case in {r['case'] for r in json.loads((E/'forward-workload-inventory.json').read_text())['records']}
low_priority_single_core()
record_name=args.record or f'case{case}-packed-compilation-plan.json'
assert Path(record_name).name==record_name and re.fullmatch(f'case{case}-packed-compilation(?:-retry[0-9]{{2}})?-plan.json',record_name)
record=E/record_name;assert not record.exists()
pilot=json.loads((E/'packed-compilation-benchmark.json').read_text())
assert pilot['status']=='IDENTICAL_PROOF_BODY_PACKING_COMPARISON_PASSED'
assert pilot['packed_seconds']<.75*pilot['individual_seconds']
h=build_helpers(K,B,transport_root)
archive=Path(args.source_archive) if args.source_archive else transport_root/f'.t03-runtime-sync-forward-case{case}-assembly-task.zip'
if args.source_archive:
 assert args.expected_source_sha256 and re.fullmatch('[0-9a-f]{64}',args.expected_source_sha256)
 assert archive.resolve().is_relative_to(scratch)
 actual=hashlib.sha256()
 with archive.open('rb') as source_file:
  while block:=source_file.read(1024*1024):actual.update(block)
 assert actual.hexdigest()==args.expected_source_sha256
keys=h['archive_info'](archive)
tainted=set();cold=set();graph={};source_hashes={};external={}
with zipfile.ZipFile(archive) as z:
    manifest=json.loads(z.read('source-sync-manifest.json'))
    task=json.loads(z.read(f'forward-case{case}-assembly-task.json'))
    for module,key in keys.items():
        name='project/'+module.replace('.','/')+'.lean';raw=z.read(name)
        assert hashlib.sha256(raw).hexdigest()==manifest[name]
        imports=[]
        for line in raw.decode().splitlines():
            if line.startswith('import '):imports.extend(line[7:].split('--')[0].split())
        deps=[m for m in imports if m=='ElevenSquare' or m.startswith('ElevenSquare.')]
        assert all(d in graph for d in deps),module
        graph[module]=deps;external[module]=[m for m in imports if m not in deps]
        source_hashes[module]=manifest[name]
        if not h['valid'](module,key):cold.add(module)
        if module in cold or any(d in tainted for d in deps):
            assert module.startswith('ElevenSquare.Tasks.T03.'),('Frozen source must remain imported',module)
            tainted.add(module)
    assert task['modules'][0] in tainted and len(tainted)>100
    order=[m for m in keys if m in tainted]
    batch=re.search(r'\.Batch(\d+)\.',task['modules'][0]).group(1)
    root_prefix=f'ElevenSquare.Tasks.T03.Batch{batch}.Case{case}.Packed'
    groups=[];current=[];size=0
    for module in order:
        raw=z.read('project/'+module.replace('.','/')+'.lean')
        if current and (len(current)>=64 or size+len(raw)>8*1024*1024):groups.append(current);current=[];size=0
        current.append(module);size+=len(raw)
    if current:groups.append(current)
    mapping={m:root_prefix+f'.Chunk{i:03d}' for i,g in enumerate(groups) for m in g}
    frontiers={}
    for i,group in enumerate(groups):
        own=root_prefix+f'.Chunk{i:03d}';imports={'ElevenSquare.Tasks.T03.KernelBoolRefl'}
        for module in group:
            imports.update(external[module])
            for dep in graph[module]:
                mapped=mapping.get(dep,dep)
                if mapped!=own:imports.add(mapped)
        frontiers[own]=sorted(imports)
    original_sha=hashlib.sha256()
    with archive.open('rb') as f:
        while block:=f.read(1024*1024):original_sha.update(block)
    payload=dict(status='EXACT_SOURCE_GROUPING_PLAN_NOT_LEAN_CHECKED',case=case,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 original_task=task,source_archive=str(archive),source_archive_sha256=original_sha.hexdigest(),
                 genuine_receipt_cold_modules=len(cold),grouped_modules=len(order),groups=groups,chunk_imports=frontiers,
                 source_hashes=source_hashes,original_source_closure_keys=keys,graph=graph,
                 root_module=mapping[task['modules'][0]],cold_modules=sorted(cold),lean_processes_started=0,
                 maximum_group_modules=64,maximum_original_body_bytes=8*1024*1024,
                 rule='Group every cold module and its dependents; imported warm frontier has no grouped ancestor.')
    record.write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:v for k,v in payload.items() if k not in ['groups','chunk_imports','source_hashes','original_source_closure_keys','graph','cold_modules']}),flush=True)
