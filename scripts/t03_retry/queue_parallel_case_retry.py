"""Retire one serial case at a compiler boundary and queue its exact grouped retry.

The original transport, sources, objects and genuine checker receipts remain.
The retry is guarded until the parallel producer obtains all dependency audits.
"""
from pathlib import Path
import argparse, datetime, fcntl, hashlib, json, os, signal, time

from retry_paths import kit_paths, low_priority_single_core
ap = argparse.ArgumentParser()
ap.add_argument('--case', type=int, required=True)
ap.add_argument('--worker', required=True)
ap.add_argument('--kit', required=True)
ap.add_argument('--runtime-root', required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--max-workers', type=int, default=1)
args = ap.parse_args()
case, worker = args.case, args.worker
_, E, transport_root = kit_paths(args.kit, args.transport_dir)
B = Path(args.runtime_root).resolve(); assert B.is_dir()
assert 1 <= args.max_workers <= 6
assert worker in ['primary', 'independent-probe', 'helper-probe', 'extra-a']
low_priority_single_core()
lock = (B / f'case{case}-parallel-retry-transition.lock').open('a')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)

def sha(path):
    result = hashlib.sha256()
    with path.open('rb') as source:
        while block := source.read(1024 * 1024):
            result.update(block)
    return result.hexdigest()

def argv(pid):
    try:
        return Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0')
    except OSError:
        return []

def descendants(pid):
    table = {}
    for path in Path('/proc').glob('[0-9]*/stat'):
        try:
            fields = path.read_text().rsplit(')', 1)[1].split()
            table[int(path.parent.name)] = (int(fields[1]), fields[0])
        except OSError:
            pass
    owned = {pid}
    changed = True
    while changed:
        changed = False
        for child, (parent, state) in table.items():
            if parent in owned and child not in owned:
                owned.add(child)
                changed = True
    return {p for p in owned - {pid} if table.get(p, (0, 'Z'))[1] != 'Z'}

def atomic_json(path, payload):
    temporary = path.with_suffix('.writing.json')
    temporary.write_text(json.dumps(payload, indent=2) + '\n')
    temporary.replace(path)

prep = json.loads((E / f'case{case}-packed-namespaced-publication.json').read_text())
assert prep['case'] == case and not prep['canonical_task_publication']
assert prep['status'] == 'PACKED_CASE_PREPARED_NOT_LEAN_CHECKED_OR_DISPATCHED'
retry = prep['task']
assert Path(retry).name == retry and retry.startswith(f'forward-case{case}-')
archive = transport_root / ('.t03-runtime-sync-' + Path(retry).stem + '.zip')
assert sha(archive) == prep['archive_sha256']
original_task = f'forward-case{case}-assembly-task.json'
original_archive = transport_root / ('.t03-runtime-sync-' + Path(original_task).stem + '.zip')
assert sha(original_archive) == prep['original_archive_sha256']
prepared = E / ('.prepared-' + retry)
new_bytes = prepared.read_bytes()
new_task = json.loads(new_bytes)
assert new_task['axiom_targets'] == json.loads((E / original_task).read_text())['axiom_targets'] == prep['axiom_targets']
assert new_task['modules'] == [prep['root_module']]
assert not (E / retry).exists()
guard = E / f'.collision-bool-preparing-case{case}.json'
record = E / f'case{case}-parallel-retry-transition.json'
publication = E / f'case{case}-packed-parallel-publication.json'
assert not guard.exists() and not record.exists() and not publication.exists()
assert case not in {r['case'] for r in json.loads((E / 'RESULT.json').read_text())['audited_case_certificates']}

dispatchers = [int(p.parent.name) for p in Path('/proc').glob('[0-9]*/cmdline')
               if any(a.endswith(b'/run_unified_proof_pool_v7.py') for a in argv(int(p.parent.name)))]
assert len(dispatchers) == 1
dispatcher = dispatchers[0]
os.kill(dispatcher, signal.SIGSTOP)
try:
    job = json.loads((E / 'unified-proof-pool-status.json').read_text())['active'][worker]
    assert job['case'] == case and job['task'] == original_task and job['kind'] == 'case'
    root = job['pid']
    assert original_task.encode() in argv(root) and any(a.endswith(b'/run_independent_probe.py') for a in argv(root))
    checkers = [p for p in descendants(root) if any(a.endswith(b'scripts/check_handoff.py') for a in argv(p))]
    assert len(checkers) == 1
    checker = checkers[0]
    with guard.open('x') as output:
        json.dump(dict(status='EXACT_GROUPED_RETRY_HELD_FOR_PARALLEL_DEPENDENCY_AUDITS', case=case,
                       retry_task=retry, maximum_parallel_lean_checks=args.max_workers), output, indent=2)
        output.write('\n')
finally:
    os.kill(dispatcher, signal.SIGCONT)

events = []
retired = False
def event(**row):
    row['utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    events.append(row)
    atomic_json(record, dict(case=case, events=events, old_job=job, retry_task=retry,
                            old_archive_preserved=str(original_archive), maximum_parallel_lean_checks=args.max_workers,
                            genuine_registered_receipts_and_objects_preserved=True,
                            current_compiler_object_may_require_original_checker_revalidation=True,
                            full_case_and_final_target_audits_pending=True))
    print(json.dumps(row), flush=True)

try:
    os.kill(root, signal.SIGSTOP)
    os.kill(checker, signal.SIGSTOP)
    event(status='CURRENT_COMPILER_ALLOWED_TO_FINISH', checker_pid=checker, current_children=sorted(descendants(checker)))
    deadline = time.monotonic() + 180
    while descendants(checker):
        if time.monotonic() > deadline:
            raise RuntimeError('Compiler boundary not reached; resume original case unchanged.')
        time.sleep(.25)
    event(status='COMPILER_BOUNDARY_REACHED_NO_LEAN_PROCESS_INTERRUPTED')
    os.kill(checker, signal.SIGTERM)
    os.kill(checker, signal.SIGCONT)
    os.kill(root, signal.SIGCONT)
    deadline = time.monotonic() + 20
    while original_task.encode() in argv(root):
        if time.monotonic() > deadline:
            raise RuntimeError('Original wrapper still live; do not dispatch duplicate work.')
        time.sleep(.1)
    retired = True
    prefix = {'independent-probe': 'independent', 'helper-probe': 'helper'}.get(worker, worker)
    execution = json.loads((E / (prefix + '-' + Path(original_task).stem + '.json')).read_text())
    assert execution['exit_code'] == 130 and execution['transport_sha256'] == prep['original_archive_sha256']
    event(status='ORIGINAL_SERIAL_CASE_RETIRED_AT_COMPILER_BOUNDARY', actual_exit_code=130,
          meaning='Deliberate performance checkpoint, not a mathematical failure or complete case audit.')
    assert sha(archive) == prep['archive_sha256'] and prepared.read_bytes() == new_bytes
    prepared.rename(E / retry)
    payload = dict(status='EXACT_GROUPED_PARALLEL_CASE_RETRY_PUBLISHED_FULL_AUDIT_PENDING', case=case,
                   utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), task=retry,
                   grouped_archive_sha256=prep['archive_sha256'], original_archive_sha256=prep['original_archive_sha256'],
                   original_archive_preserved=str(original_archive), root_module=prep['root_module'],
                   original_target=prep['axiom_targets'], groups=prep['groups'],
                   grouped_modules=prep['original_modules_grouped'],
                   original_canonical_source_files_and_numeric_data_unchanged=True,
                   maximum_parallel_checks=args.max_workers, full_case_guard_retained_for_parallel_dependency_audits=True,
                   full_case_and_final_target_audits_pending=True)
    atomic_json(publication, payload)
    event(status='PARALLEL_GROUP_PRODUCER_MAY_START', publication=publication.name,
          groups=prep['groups'], grouped_modules=prep['original_modules_grouped'], full_case_guard_retained=True)
except Exception as exc:
    event(status='TRANSITION_ERROR_REQUIRES_INSPECTION', error=repr(exc), original_checker_retired=retired)
    raise
finally:
    for pid in [checker, root]:
        try:
            os.kill(pid, signal.SIGCONT)
        except ProcessLookupError:
            pass
    if not retired and not (E / retry).exists() and guard.exists():
        assert json.loads(guard.read_text())['retry_task'] == retry
        guard.unlink()
