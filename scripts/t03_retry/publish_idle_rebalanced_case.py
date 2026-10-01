"""Publish a distinct retry for an idle prepacked case; retain its old sources."""
from pathlib import Path
import argparse, ctypes, datetime, hashlib, json, os

ap = argparse.ArgumentParser()
ap.add_argument('--case', type=int, required=True)
ap.add_argument('--revision', type=int, default=1)
ap.add_argument('--kit',required=True);ap.add_argument('--transport-dir');ap.add_argument('--max-workers',type=int,default=1)
a = ap.parse_args()
from retry_paths import kit_paths,low_priority_single_core
K,E,transport_root=kit_paths(a.kit,a.transport_dir)
assert 1<=a.max_workers<=6
low_priority_single_core()
assert 1 <= a.revision <= 99
case = a.case
def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()

prep_name = f'case{case}-packed-namespaced-retry{a.revision:02d}-publication.json'
prep = json.loads((E / prep_name).read_text())
old_prep = json.loads((E / f'case{case}-packed-namespaced-publication.json').read_text())
old_pub_path = E / f'case{case}-packed-canonical-publication.json'
old_pub_raw = old_pub_path.read_bytes()
old_pub = json.loads(old_pub_raw)
assert prep['case'] == old_pub['case'] == case
assert prep['status'] == 'PACKED_CASE_PREPARED_NOT_LEAN_CHECKED_OR_DISPATCHED'
assert not prep['canonical_task_publication']
assert prep['original_sources_and_data_unchanged'] and prep['numeric_tokens_unchanged']
assert prep['original_archive_sha256'] == old_pub['original_archive_sha256']
assert prep['exact_certificate_header'] == old_prep['exact_certificate_header']
assert prep['axiom_targets'] == old_pub['original_target']
assert prep['group_module_prefix'] == prep['root_module'].rsplit('.', 1)[0] + '.'
new_task_name = prep['task']
assert Path(new_task_name).name == new_task_name and new_task_name.startswith(f'forward-case{case}-')
new_task = E / new_task_name
prepared = E / ('.prepared-' + new_task_name)
old_task = E / f'forward-case{case}-assembly-task.json'
held_task = E / (f'.held-for-rebalanced-case{case}-' + old_task.name)
record = E / f'case{case}-idle-rebalanced-local-publication.json'
publication = E / f'case{case}-packed-parallel-publication.json'
assert not new_task.exists() and prepared.exists() and old_task.exists()
assert not held_task.exists() and not record.exists() and not publication.exists()
assert old_task.resolve().parent == held_task.resolve().parent == new_task.resolve().parent == E.resolve()
old_task_raw = old_task.read_bytes()
new_task_raw = prepared.read_bytes()
assert json.loads(new_task_raw)['axiom_targets'] == json.loads(old_task_raw)['axiom_targets'] == prep['axiom_targets']
assert json.loads(new_task_raw)['modules'] == [prep['root_module']]
new_archive = transport_root / ('.t03-runtime-sync-' + Path(new_task_name).stem + '.zip')
old_archive = transport_root / ('.t03-runtime-sync-' + Path(old_task.name).stem + '.zip')
assert sha(new_archive) == prep['archive_sha256']
assert sha(old_archive) == old_pub['grouped_archive_sha256']
guard = E / f'.collision-bool-preparing-case{case}.json'
old_guard_raw = guard.read_bytes()
assert json.loads(old_guard_raw)['status'] == 'NEW_CASE_TASK_HELD_FOR_EXTERNAL_CERTIFICATE_REUSE'
pool = json.loads((E / 'unified-proof-pool-status.json').read_text())
assert not any(j.get('case') == case or j['task'].startswith(f'library-case{case}-')
               for j in pool['active'].values())
assert case not in {r['case'] for r in json.loads((E / 'RESULT.json').read_text())['audited_case_certificates']}
assert not (E / f'library-case{case}-node998-queue.json').exists()
saved_guard = E / f'case{case}-external-reuse-hold-before-local-resume.json'
saved_pub = E / f'case{case}-greedy-canonical-publication-before-local-retry.json'
assert not saved_guard.exists() and not saved_pub.exists()
saved_guard.write_bytes(old_guard_raw)
saved_pub.write_bytes(old_pub_raw)
old_task.rename(held_task)
assert held_task.read_bytes() == old_task_raw
prepared.rename(new_task)
assert new_task.read_bytes() == new_task_raw
p = dict(status='IDLE_CASE_REBALANCED_LOCAL_RETRY_PUBLISHED_FULL_AUDIT_PENDING', case=case,
         utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), task=new_task_name,
         preparation=prep_name, grouped_archive_sha256=prep['archive_sha256'],
         original_archive_sha256=prep['original_archive_sha256'],
         old_greedy_archive_preserved=str(old_archive), old_greedy_archive_sha256=old_pub['grouped_archive_sha256'],
         old_greedy_task_preserved=held_task.name, old_greedy_task_sha256=hashlib.sha256(old_task_raw).hexdigest(),
         original_target=prep['axiom_targets'], root_module=prep['root_module'],
         groups=prep['groups'], grouped_modules=prep['original_modules_grouped'],
         original_canonical_source_files_and_numeric_data_unchanged=True,
         full_case_guard_retained_for_parallel_dependency_audits=True,
         maximum_parallel_checks=a.max_workers, maximum_live_chunk_archives=2,
         actual_case_certificate_and_final_return_audits_pending=True)
publication.write_text(json.dumps(p, indent=2) + '\n')
record.write_text(json.dumps(p, indent=2) + '\n')
guard.write_text(json.dumps(dict(status='EXACT_GROUPED_RETRY_HELD_FOR_PARALLEL_DEPENDENCY_AUDITS',
    case=case, utc=p['utc'], retry_task=new_task_name, source_archive_sha256=prep['archive_sha256'],
    required_dependency_groups=prep['groups'], maximum_parallel_lean_checks=a.max_workers,
    prior_hold=saved_guard.name, full_case_and_final_audits_pending=True), indent=2) + '\n')
print(json.dumps(p), flush=True)
