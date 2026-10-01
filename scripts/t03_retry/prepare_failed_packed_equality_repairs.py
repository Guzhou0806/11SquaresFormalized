"""Repair failed/never-issued equality constructions; preserve every live closure.

Only ordinary reflexivity proof construction changes. All resulting declarations
and the exact full-case target still require the original Lean checker.
"""
from pathlib import Path
import argparse, ctypes, datetime, hashlib, json, os, re, zipfile
from retry_paths import kit_paths, low_priority_single_core, metadata_path
ap = argparse.ArgumentParser()
ap.add_argument('--case',type=int,required=True)
ap.add_argument('--kit',required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--scratch-root',required=True)
ap.add_argument('--max-workers',type=int,default=1)
ap.add_argument('--source-root')
ap.add_argument('--revision', type=int, default=1)
ap.add_argument('--failed-group', action='append', default=[])
args = ap.parse_args()
case = args.case
K,E,transport_root=kit_paths(args.kit,args.transport_dir)
S=Path(args.source_root).resolve() if args.source_root else K/'eleven-square-lean'
assert 1<=args.max_workers<=6
low_priority_single_core()
assert 1 <= args.revision <= 99
revision_tag = '' if args.revision == 1 else f'-retry{args.revision:02d}'
failed_settings = {1464: [(203, 'library-b'), (209, 'extra-a')],
                   1465: [(107, 'library-b'), (108, 'independent')]}
assert case in failed_settings
if args.failed_group:
    failed_settings[case] = [(int(item.split(':',1)[0]), item.split(':',1)[1]) for item in args.failed_group]
    assert all(prefix in ['primary','independent','helper','extra-a','library-a','library-b','library-c'] for _,prefix in failed_settings[case])
else:
    assert args.revision == 1
checkpoint = json.loads((E / f'case{case}-equality-repair-producer-checkpoint{revision_tag}.json').read_text())
assert checkpoint['stopped_at_complete_file_boundary'] and checkpoint['proof_processes_signalled'] == []
pilot = json.loads((E / 'equality-refl-benchmark.json').read_text())
assert pilot['kernel_negative_control_rejected'] and pilot['measured_gain']
record = E / f'case{case}-equality-refl{revision_tag}-publication.json'
ready = transport_root / f'.t03-equality-case{case}{revision_tag}-ready.zip'
assert not record.exists() and not ready.exists()
publication_path = E / f'case{case}-packed-parallel-publication.json'
publication = json.loads(publication_path.read_text())
assert publication['full_case_guard_retained_for_parallel_dependency_audits']
prep = json.loads((E / f'case{case}-packed-namespaced-publication.json').read_text())
master = transport_root / ('.t03-runtime-sync-' + Path(prep['task']).stem + '.zip')
queue_path = E / f'library-case{case}-node998-queue.json'
queue_raw = queue_path.read_bytes()
queue = json.loads(queue_raw)
rows = queue['tasks']
graph = {r['module']:r['dependencies'] for r in rows}
scratch=Path(args.scratch_root).resolve();assert scratch.is_dir()
destination=scratch/f'case{case}-parallel-packed-transports'
backup = scratch / (f'case{case}-failed-equality-repair-' + datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
assert backup.resolve().parent == scratch.resolve() and not backup.exists()
backup.mkdir()
(backup / queue_path.name).write_bytes(queue_raw)
(backup / publication_path.name).write_bytes(publication_path.read_bytes())
changed_dir = backup / 'changed-sources'
original_dir = backup / 'original-sources'
changed_dir.mkdir(); original_dir.mkdir()

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as source:
        while block := source.read(1024 * 1024):
            h.update(block)
    return h.hexdigest()

old_sha = sha(master)
assert old_sha == publication['grouped_archive_sha256']
failed = {}
aliases = {}
prior_transition = publication.get('kernel_equality_refl_transition')
if prior_transition:
    prior = json.loads((E / prior_transition).read_text())
    assert prior['status'] == 'FAILED_AND_UNPUBLISHED_GROUP_EQUALITY_PROOFS_CANONICALLY_PUBLISHED'
    assert prior['new_grouped_archive_sha256'] == old_sha
    aliases.update(prior.get('group_task_aliases', {}))
for number, prefix in failed_settings[case]:
    row = next(r for r in rows if r['module'].endswith(f'.Chunk{number:03d}'))
    task_name = row['task']
    execution_path = E / (prefix + '-' + Path(task_name).stem + '.json')
    execution = json.loads(execution_path.read_text())
    assert execution['exit_code'] == 1 and execution['task'] == task_name
    wrapper = (E / (prefix + '-' + Path(task_name).stem + '.log')).read_text(encoding='utf8')
    actual_log = re.findall(r'^Log: ([^\n]+/lean\.log)$', wrapper, re.M)[-1]
    log_path=metadata_path(actual_log)
    log_raw = log_path.read_bytes()
    check = json.loads(log_path.with_name('CHECK.json').read_text())
    assert check['exit_code'] == 1 and check['source'].endswith(f'Case{case}/PackedNamespaced/Chunk{number:03d}.lean')
    error_lines = [line for line in log_raw.decode().splitlines() if ': error:' in line]
    assert error_lines and all('The rfl tactic failed' in line or 'unsolved goals' in line for line in error_lines)
    locations = sorted(set(int(n) for n in re.findall(rb'Chunk\d+\.lean:(\d+):\d+: error: The rfl tactic failed', log_raw)))
    assert locations
    archive = transport_root / ('.t03-runtime-sync-' + Path(task_name).stem + '.zip')
    assert archive.exists() and not (destination / archive.name).exists()
    assert sha(archive) == execution['transport_sha256']
    stem = re.sub(r'-equality-retry[0-9]+$', '', Path(task_name).stem.removesuffix('-task'))
    retry = stem + f'-equality-retry{args.revision:02d}-task.json'
    assert retry.startswith(f'library-case{case}-node998-')
    assert not (E / retry).exists() and not (E / ('.prepared-' + retry)).exists()
    task_raw = (E / task_name).read_bytes()
    task = json.loads(task_raw)
    assert task['modules'] == [row['module']] and task['axiom_targets'] == row['axiom_targets']
    aliases[row['module']] = retry
    failed[row['module']] = dict(old_task=task_name, retry_task=retry,
        original_failed_archive=str(archive), original_failed_archive_sha256=execution['transport_sha256'],
        actual_failed_log=actual_log, actual_failed_log_sha256=hashlib.sha256(log_raw).hexdigest(),
        failed_rfl_source_lines=locations, actual_failed_CHECK=check, prepared_task_sha256=hashlib.sha256(task_raw).hexdigest())
    (backup / retry).write_bytes(task_raw)
published = set()
for row in rows:
    archive_name = '.t03-runtime-sync-' + Path(row['task']).stem + '.zip'
    if (transport_root / archive_name).exists() or (destination / archive_name).exists():
        published.add(row['module'])
assert set(failed) <= published
preserved = set()
def preserve(module):
    if module in preserved:
        return
    assert module not in failed, ('An issued group depends on an unrepaired failed group', module)
    for dependency in graph[module]:
        preserve(dependency)
    preserved.add(module)
for module in published - set(failed):
    preserve(module)
active = json.loads((E / 'unified-proof-pool-status.json').read_text())['active']
assert not any(j['task'] in {r['old_task'] for r in failed.values()} for j in active.values())
pattern = re.compile(r'(?<=by )rfl\b|(?<=<;> )rfl\b')
helper_name = 'project/ElevenSquare/Tasks/T03/KernelEqualityRefl.lean'
bindings = []
temporary = backup / 'new-master.zip'
with zipfile.ZipFile(master) as source:
    manifest = json.loads(source.read('source-sync-manifest.json'))
    assert manifest[helper_name] == '579aba76120723d18a2d3ee1464e136612cca06ef76f9547a67ae183b2c92200'
    full_task_raw = source.read(prep['task'])
    full_task = json.loads(full_task_raw)
    assert full_task['axiom_targets'] == [f'ElevenSquare.Pending.T03.Batch04.Case{case}.Forward.Certificate.certificate_exists']
    new_manifest = dict(manifest)
    modules = {'project/' + r['module'].replace('.', '/') + '.lean':r['module'] for r in rows}
    with zipfile.ZipFile(temporary, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=1) as output:
        for name, expected in manifest.items():
            raw = source.read(name)
            assert hashlib.sha256(raw).hexdigest() == expected
            data = raw
            module = modules.get(name)
            if module and module not in preserved:
                assert (S / name[8:]).read_bytes() == raw
                text = raw.decode('utf8')
                if module in failed:
                    assert all(pattern.search(text.splitlines()[n-1]) for n in failed[module]['failed_rfl_source_lines'])
                changed, count = pattern.subn('t03_eq_refl', text)
                if count:
                    if 'import ElevenSquare.Tasks.T03.KernelEqualityRefl\n' not in changed:
                        changed = 'import ElevenSquare.Tasks.T03.KernelEqualityRefl\n' + changed
                    assert re.findall(r'\b[0-9]+\b', text) == re.findall(r'\b[0-9]+\b', changed)
                    data = changed.encode('utf8')
                    assert len(data) < 16 * 1024 * 1024
                    (original_dir / Path(name).name).write_bytes(raw)
                    (changed_dir / Path(name).name).write_bytes(data)
                    bindings.append(dict(module=module, old_source_sha256=expected,
                                         new_source_sha256=hashlib.sha256(data).hexdigest(), equalities=count))
                    new_manifest[name] = hashlib.sha256(data).hexdigest()
            output.writestr(name, data)
        output.writestr('source-sync-manifest.json', json.dumps(new_manifest))
assert set(failed) <= {r['module'] for r in bindings}
with zipfile.ZipFile(temporary) as checked:
    assert len(checked.namelist()) == len(set(checked.namelist()))
    assert set(checked.namelist()) == set(new_manifest) | {'source-sync-manifest.json'}
    assert checked.read(prep['task']) == full_task_raw
    for name, expected in new_manifest.items():
        assert hashlib.sha256(checked.read(name)).hexdigest() == expected
assert sha(master) == old_sha
with temporary.open('rb') as source, ready.open('xb') as output:
    while block := source.read(1024 * 1024):
        output.write(block)
new_sha = sha(ready)
assert new_sha == sha(temporary)
for row in bindings:
    path = S / (row['module'].replace('.', '/') + '.lean')
    assert sha(path) == row['old_source_sha256']
    path.write_bytes((changed_dir / path.name).read_bytes())
for module, failure in failed.items():
    retry = failure['retry_task']
    (E / ('.prepared-' + retry)).write_bytes((backup / retry).read_bytes())
p = dict(status='FAILED_AND_UNPUBLISHED_GROUP_EQUALITY_PROOFS_PREPARED_ALL_NEW_PROOFS_PENDING',
    case=case, utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    repair_revision=args.revision, prior_equality_transition=prior_transition,
    previous_grouped_archive_sha256=old_sha, new_grouped_archive_sha256=new_sha,
    ready_archive=str(ready), backup_directory=str(backup), new_verified_archive=str(temporary),
    publication_file=publication_path.name, queue_file=queue_path.name,
    modified_groups=len(bindings), changed_equality_proof_constructions=sum(r['equalities'] for r in bindings),
    failed_groups=failed, group_task_aliases=aliases, modified_source_bindings=bindings,
    preserved_published_modules=sorted(preserved), numeric_tokens_unchanged=True,
    all_unaffected_published_and_running_group_source_closures_unchanged=True,
    original_certificate_type_and_root_unchanged=True, maximum_running_lean_checks=args.max_workers,
    proof_processes_signalled=[], full_case_and_final_audits_pending=True,
    new_proof_construction='Ordinary Eq.refl of unchanged right side; original kernel must check each declaration.')
record.write_text(json.dumps(p, indent=2) + '\n')
print(json.dumps({k:v for k,v in p.items() if k not in ['modified_source_bindings','preserved_published_modules','failed_groups']}), flush=True)
