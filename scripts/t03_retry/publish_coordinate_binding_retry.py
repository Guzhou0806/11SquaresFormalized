"""Publish a prepared repair in the existing pool, preserving the old reuse hold."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, signal, zipfile
from retry_paths import kit_paths, low_priority_single_core
ap = argparse.ArgumentParser()
ap.add_argument('--case', type=int, required=True)
ap.add_argument('--kit', required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--dispatcher-name', default='run_unified_proof_pool_v7.py')
ap.add_argument('--max-workers', type=int, default=1)
args = ap.parse_args(); case = args.case
K, E, transport_root = kit_paths(args.kit, args.transport_dir)
assert Path(args.dispatcher_name).name == args.dispatcher_name
assert 1 <= args.max_workers <= 6
low_priority_single_core()
record = E / f'case{case}-coordinate-binding-retry-publication.json'
p = json.loads(record.read_text())
assert p['status'] == 'KERNEL_CHECKED_COORDINATE_BINDING_REPAIRS_PREPARED_FULL_CASE_AUDIT_PENDING'
assert p['maximum_running_lean_checks'] == args.max_workers
name = p['retry_task']
assert Path(name).name == name
prepared = E / ('.prepared-' + name)
target = E / name
assert prepared.is_file() and not target.exists()
archive = transport_root / ('.t03-runtime-sync-' + Path(name).stem + '.zip')
h = hashlib.sha256()
with archive.open('rb') as source:
    while block := source.read(1024 * 1024):
        h.update(block)
assert h.hexdigest() == p['retry_archive_sha256']
with zipfile.ZipFile(archive) as z:
    assert z.read(name) == prepared.read_bytes()
guard = E / f'.collision-bool-preparing-case{case}.json'
old_guard = guard.read_bytes()
assert json.loads(old_guard)['status'] == 'NEW_CASE_TASK_HELD_FOR_EXTERNAL_CERTIFICATE_REUSE'
assert json.loads(old_guard)['case'] == case
backup = E / f'case{case}-external-reuse-hold-before-binding-retry.json'
assert not backup.exists()
def argv(pid):
    try:
        return Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0')
    except OSError:
        return []
dispatchers = [int(q.parent.name) for q in Path('/proc').glob('[0-9]*/cmdline')
               if any(a.endswith(('/' + args.dispatcher_name).encode()) for a in argv(int(q.parent.name)))]
assert len(dispatchers) == 1
dispatcher = dispatchers[0]
os.kill(dispatcher, signal.SIGSTOP)
try:
    assert all(j.get('case') != case and not j.get('task', '').startswith((f'library-case{case}-', f'forward-case{case}-')) for j in json.loads((E / 'unified-proof-pool-status.json').read_text())['active'].values())
    assert case not in {r['case'] for r in json.loads((E / 'RESULT.json').read_text())['audited_case_certificates']}
    assert guard.read_bytes() == old_guard
    with backup.open('xb') as saved:
        saved.write(old_guard)
    prepared.rename(target)
    guard.unlink()
    p.update(status='KERNEL_CHECKED_COORDINATE_BINDING_REPAIRS_QUEUED_FULL_CASE_AUDIT_PENDING',
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), published_task=str(target),
        prior_full_case_attempt_failed=True, prior_failure_wrapper=f'extra-a-forward-case{case}-assembly-task.log',
        previous_external_reuse_hold_preserved=backup.name,
        previous_external_reuse_hold_sha256=hashlib.sha256(old_guard).hexdigest(),
        reason='Apply the actual accepted exact-data binding repair while the external certificate source handoff remains unavailable.',
        running_proof_workers_unchanged=True)
    temporary = record.with_suffix('.writing.json')
    temporary.write_text(json.dumps(p, indent=2) + '\n')
    temporary.replace(record)
    print(json.dumps(p), flush=True)
finally:
    os.kill(dispatcher, signal.SIGCONT)
