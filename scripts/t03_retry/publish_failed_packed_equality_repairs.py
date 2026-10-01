"""Publish exact repairs and distinct retry tasks without touching Lean workers."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, shutil, signal, zipfile
from retry_paths import kit_paths, low_priority_single_core, metadata_path
ap = argparse.ArgumentParser()
ap.add_argument('--case',type=int,required=True)
ap.add_argument('--kit',required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--scratch-root',required=True)
ap.add_argument('--max-workers',type=int,default=1)
ap.add_argument('--dispatcher-name',default='run_unified_proof_pool_v7.py')
args=ap.parse_args();case=args.case
K,E,transport_root=kit_paths(args.kit,args.transport_dir)
scratch=Path(args.scratch_root).resolve();assert scratch.is_dir()
assert 1<=args.max_workers<=6 and Path(args.dispatcher_name).name==args.dispatcher_name
assert case in (1464, 1465)
low_priority_single_core()
record = E / f'case{case}-equality-refl-publication.json'
p = json.loads(record.read_text())
assert p['status'] == 'FAILED_AND_UNPUBLISHED_GROUP_EQUALITY_PROOFS_PREPARED_ALL_NEW_PROOFS_PENDING'
assert p['all_unaffected_published_and_running_group_source_closures_unchanged']
assert p['maximum_running_lean_checks']==args.max_workers
prep = json.loads((E / f'case{case}-packed-namespaced-publication.json').read_text())
master = transport_root / ('.t03-runtime-sync-' + Path(prep['task']).stem + '.zip')
def posix(path):
    return metadata_path(path)

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as source:
        while block := source.read(1024 * 1024):
            h.update(block)
    return h.hexdigest()
ready = posix(p['ready_archive'])
backup = posix(p['backup_directory'])
assert backup.resolve().parent == scratch
assert ready.resolve().parent == master.resolve().parent == transport_root.resolve()
assert sha(master) == p['previous_grouped_archive_sha256']
assert sha(ready) == p['new_grouped_archive_sha256']
publication_path = E / p['publication_file']
publication_raw = publication_path.read_bytes()
publication = json.loads(publication_raw)
assert publication['grouped_archive_sha256'] == p['previous_grouped_archive_sha256']
assert (backup / publication_path.name).read_bytes() == publication_raw
queue_path = E / p['queue_file']
queue_raw = queue_path.read_bytes()
assert (backup / queue_path.name).read_bytes() == queue_raw
queue = json.loads(queue_raw)
with zipfile.ZipFile(master) as old, zipfile.ZipFile(ready) as new:
    old_manifest = json.loads(old.read('source-sync-manifest.json'))
    new_manifest = json.loads(new.read('source-sync-manifest.json'))
    changed = {n for n,v in old_manifest.items() if new_manifest.get(n) != v}
    assert set(old_manifest) == set(new_manifest)
    assert changed == {'project/' + r['module'].replace('.', '/') + '.lean' for r in p['modified_source_bindings']}
    assert old.read(prep['task']) == new.read(prep['task'])
    # Every previously issued unaffected closure stays byte-for-byte identical.
    destination = scratch/f'case{case}-parallel-packed-transports'
    for row in queue['tasks']:
        if row['module'] not in p['preserved_published_modules']:
            continue
        filename = '.t03-runtime-sync-' + Path(row['task']).stem + '.zip'
        paths = [q for q in [transport_root / filename, destination / filename] if q.exists()]
        assert paths
        for path in paths:
            with zipfile.ZipFile(path) as issued:
                issued_manifest = json.loads(issued.read('source-sync-manifest.json'))
                for name, expected in issued_manifest.items():
                    if name == row['task']:
                        assert hashlib.sha256((E / name).read_bytes()).hexdigest() == expected
                    else:
                        assert new_manifest[name] == expected, ('Changed a live/accepted closure', row['module'], name)
for module, retry in p['group_task_aliases'].items():
    prepared = E / ('.prepared-' + retry)
    assert prepared.read_bytes() == (backup / retry).read_bytes() and not (E / retry).exists()
    assert hashlib.sha256(prepared.read_bytes()).hexdigest() == p['failed_groups'][module]['prepared_task_sha256']
failed_destination = backup / 'original-failed-transports'
failed_destination.mkdir()
for module, failed in p['failed_groups'].items():
    old_path = posix(failed['original_failed_archive'])
    assert old_path.resolve().parent == transport_root.resolve()
    assert sha(old_path) == failed['original_failed_archive_sha256']
    saved = failed_destination / old_path.name
    shutil.copyfile(old_path, saved)
    assert sha(saved) == failed['original_failed_archive_sha256']
    failed['preserved_failed_transport'] = str(saved)
old_master_backup = backup / master.name
shutil.copyfile(master, old_master_backup)
assert sha(old_master_backup) == p['previous_grouped_archive_sha256']
guard = E / f'.collision-bool-preparing-case{case}.json'
guard_raw = guard.read_bytes()
assert json.loads(guard_raw)['status'] == 'EXACT_GROUPED_RETRY_HELD_FOR_PARALLEL_DEPENDENCY_AUDITS'
def argv(pid):
    try:
        return Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0')
    except OSError:
        return []
controllers = [int(q.parent.name) for q in Path('/proc').glob('[0-9]*/cmdline')
               if any(a and Path(os.fsdecode(a)).resolve()==(E/args.dispatcher_name).resolve() for a in argv(int(q.parent.name)))]
assert len(controllers) == 1
controller = controllers[0]
os.kill(controller, signal.SIGSTOP)
try:
    pool = json.loads((E / 'unified-proof-pool-status.json').read_text())
    old_failed_tasks = {r['old_task'] for r in p['failed_groups'].values()}
    assert not any(j['task'] in old_failed_tasks for j in pool['active'].values())
    assert guard.read_bytes() == guard_raw
    assert queue_path.read_bytes() == queue_raw and publication_path.read_bytes() == publication_raw
    os.replace(ready, master)
    for module, failed in p['failed_groups'].items():
        old_path = posix(failed['original_failed_archive'])
        assert old_path.resolve().parent == transport_root.resolve()
        assert sha(old_path) == failed['original_failed_archive_sha256']
        old_path.unlink()
        (E / ('.prepared-' + failed['retry_task'])).rename(E / failed['retry_task'])
    for row in queue['tasks']:
        if row['module'] in p['group_task_aliases']:
            row['task'] = p['group_task_aliases'][row['module']]
    queue['equality_repair_publication'] = record.name
    temporary = queue_path.with_suffix('.writing.json')
    temporary.write_text(json.dumps(queue, indent=2) + '\n'); temporary.replace(queue_path)
    publication.update(grouped_archive_sha256=p['new_grouped_archive_sha256'],
        previous_grouped_archive_sha256=p['previous_grouped_archive_sha256'],
        kernel_equality_refl_transition=record.name, full_case_guard_retained_for_parallel_dependency_audits=True)
    temporary = publication_path.with_suffix('.writing.json')
    temporary.write_text(json.dumps(publication, indent=2) + '\n'); temporary.replace(publication_path)
    p.update(status='FAILED_AND_UNPUBLISHED_GROUP_EQUALITY_PROOFS_CANONICALLY_PUBLISHED',
        published_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        old_grouped_archive_backup=str(old_master_backup),
        original_publication_metadata_backup=str(backup / publication_path.name),
        failed_tasks_retired_original_transports_preserved=True,
        group_retry_tasks_queued_under_distinct_names=True,
        full_case_guard_retained=True, running_proof_workers_unchanged=True)
    temporary = record.with_suffix('.writing.json')
    temporary.write_text(json.dumps(p, indent=2) + '\n'); temporary.replace(record)
    print(json.dumps({k:v for k,v in p.items() if k not in ['modified_source_bindings','preserved_published_modules','failed_groups']}), flush=True)
finally:
    os.kill(controller, signal.SIGCONT)
