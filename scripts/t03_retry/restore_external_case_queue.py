"""Restore one preserved private queue after its exact local proof barrier is set."""
from pathlib import Path
import argparse, datetime, hashlib, json

ap = argparse.ArgumentParser()
ap.add_argument('--case', type=int, required=True)
ap.add_argument('--kit',required=True);ap.add_argument('--max-workers',type=int,default=1)
a=ap.parse_args();case=a.case
from retry_paths import kit_paths
K,E,_=kit_paths(a.kit)
assert 1<=a.max_workers<=6
pub = json.loads((E / f'case{case}-packed-canonical-publication.json').read_text())
guard = json.loads((E / f'.collision-bool-preparing-case{case}.json').read_text())
assert pub['case'] == guard['case'] == case
assert pub['full_case_guard_retained_for_parallel_dependency_audits']
assert guard['status'] == 'EXACT_GROUPED_RETRY_HELD_FOR_PARALLEL_DEPENDENCY_AUDITS'
assert guard['source_archive_sha256'] == pub['grouped_archive_sha256']
pool = json.loads((E / 'unified-proof-pool-status.json').read_text())
assert not any(j.get('case') == case or j['task'].startswith(f'library-case{case}-')
               for j in pool['active'].values())
held = E / f'.held-for-external-reuse-library-case{case}-node998-queue.json'
target = E / f'library-case{case}-node998-queue.json'
saved = E / f'case{case}-external-reuse-queue-before-local-resume.json'
record = E / f'case{case}-external-reuse-queue-local-resume.json'
assert held.resolve().parent == target.resolve().parent == E.resolve()
assert held.exists() and not target.exists() and not saved.exists() and not record.exists()
raw = held.read_bytes()
digest = hashlib.sha256(raw).hexdigest()
queue = json.loads(raw)
assert len(queue['tasks']) == pub['groups']
assert all(r['task'].startswith(f'library-case{case}-node998-') for r in queue['tasks'])
if 'kernel_equality_refl_transition' in pub:
    transition = json.loads((E / pub['kernel_equality_refl_transition']).read_text())
    assert transition['source_queue'] == held.name and transition['source_queue_sha256'] == digest
    assert transition['new_grouped_archive_sha256'] == pub['grouped_archive_sha256']
saved.write_bytes(raw)
assert saved.read_bytes() == raw
held.rename(target)
assert target.read_bytes() == raw
p = dict(status='PRESERVED_EXACT_PRIVATE_QUEUE_RESTORED_FOR_LOCAL_CHECKING', case=case,
         utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         restored_queue=target.name, preserved_queue_snapshot=saved.name,
         queue_sha256=digest, exact_source_archive_sha256=pub['grouped_archive_sha256'],
         dependency_groups=pub['groups'], maximum_global_compiler_checks=a.max_workers,
         existing_compiler_processes_signalled=[], accepted_case_count_changed=False,
         full_case_and_final_audits_pending=True)
record.write_text(json.dumps(p, indent=2) + '\n')
print(json.dumps(p), flush=True)
