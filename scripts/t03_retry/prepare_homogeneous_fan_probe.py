"""Queue an abstract arithmetic proof in the existing six-check compiler pool.

This is a helper check, not a full returned-case certificate or an accepted DAG
group. Original checker/environment bytes and exact reachable sources are used.
"""
from pathlib import Path
import ctypes, datetime, hashlib, json, os, re, shutil, zipfile

import argparse
from retry_paths import kit_paths,low_priority_single_core,metadata_path
ap=argparse.ArgumentParser()
ap.add_argument('--kit',required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--scratch-root',required=True)
ap.add_argument('--source-root',type=Path)
ap.add_argument('--max-workers',type=int,default=1)
a=ap.parse_args()
K,E,transport_root=kit_paths(a.kit,a.transport_dir)
S=a.source_root.resolve() if a.source_root else K/'eleven-square-lean'
scratch=Path(a.scratch_root).resolve();assert scratch.is_dir()
assert 1<=a.max_workers<=6
low_priority_single_core()
task_name = 'library-case1499-node996-homogeneous-fan-helper-probe-task.json'
module = 'ElevenSquare.Tasks.T03.HomogeneousPolygonFan'
targets = ['ElevenSquare.Pending.T03.HomPoint.fanCrossCheck_sound',
           'ElevenSquare.Pending.T03.HomEdgeCertificate.check_sound',
           'ElevenSquare.Pending.T03.homogeneousPolygonFanCheck_sound']
task = json.loads((E / 'forward-case1499-parallel-retry01-assembly-task.json').read_text())
task.update(id='T03_HOMOGENEOUS_FAN_HELPER_PROBE_NOT_CASE_EVIDENCE', modules=[module],
            axiom_targets=targets,
            check_scope='Abstract integer arithmetic bridge only; no case certificate or timing claim.')
task_raw = (json.dumps(task, indent=2) + '\n').encode()
queue = E / 'library-case1499-node996-queue.json'
assert not queue.exists() and not (E / task_name).exists()
members = {}
visiting = set()

def visit(m):
    name = 'project/' + m.replace('.', '/') + '.lean'
    if name in members:
        return
    assert m not in visiting
    visiting.add(m)
    raw = (S / name[8:]).read_bytes()
    for line in raw.decode().splitlines():
        if line.startswith('import '):
            for dep in line[7:].split('--')[0].split():
                if dep == 'ElevenSquare' or dep.startswith('ElevenSquare.'):
                    visit(dep)
    members[name] = raw
    visiting.remove(m)

visit(module)
for name in ('lakefile.lean', 'lake-manifest.json', 'lean-toolchain',
             'scripts/check_handoff.py', 'scripts/lean_small_check.py', 'scripts/lake.sh'):
    members['project/' + name] = (S / name).read_bytes()
members[task_name] = task_raw
manifest = {n: hashlib.sha256(raw).hexdigest() for n, raw in members.items()}
name = '.t03-runtime-sync-' + Path(task_name).stem + '.zip'
temporary = scratch / name
target = transport_root / name
assert not temporary.exists() and not target.exists()
with zipfile.ZipFile(temporary, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=1) as out:
    for n, raw in members.items():
        out.writestr(n, raw)
    out.writestr('source-sync-manifest.json', json.dumps(manifest))
with zipfile.ZipFile(temporary) as checked:
    assert len(checked.namelist()) == len(set(checked.namelist()))
    for n, digest in manifest.items():
        assert hashlib.sha256(checked.read(n)).hexdigest() == digest
shutil.copyfile(temporary, target)
digest = hashlib.sha256(temporary.read_bytes()).hexdigest()
assert hashlib.sha256(target.read_bytes()).hexdigest() == digest
(E / task_name).write_bytes(task_raw)
queue.write_text(json.dumps(dict(status='ABSTRACT_HELPER_PROOF_PROBE_NOT_CASE_EVIDENCE', tasks=[dict(
    task=task_name, module=module, axiom_targets=targets, dependencies=[],
    remaining_dependency_path_groups=1000)]), indent=2) + '\n')
record = dict(status='INTEGER_FAN_ABSTRACT_BRIDGE_QUEUED_LEAN_AND_TIMING_PENDING',
              utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), task=task_name,
              transport_sha256=digest, helper_sha256=manifest['project/' + module.replace('.', '/') + '.lean'],
              exact_claim='homogeneousPolygonFanCheck implies the unchanged rational polygonFanCheck',
              maximum_global_compiler_checks=a.max_workers, sources_of_running_proof_jobs_changed=False,
              case_acceptance_count_changed=False, case_checks_and_timing_comparison_pending=True)
(E / 'homogeneous-fan-helper-probe-preparation.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record), flush=True)
