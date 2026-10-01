"""Change only Lean-checked failed proof constructions in an immutable case retry."""
from pathlib import Path
import argparse, ctypes, datetime, hashlib, json, os, re, sys, zipfile
from retry_paths import kit_paths, low_priority_single_core
ap = argparse.ArgumentParser()
ap.add_argument('--case', type=int, required=True)
ap.add_argument('--kit', required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--scratch-root', required=True)
ap.add_argument('--failed-execution', help='Existing checker execution record filename; default extra-a case record')
ap.add_argument('--max-workers', type=int, default=1)
args = ap.parse_args(); case = args.case
K, E, transport_root = kit_paths(args.kit, args.transport_dir)
S = K / 'eleven-square-lean'
scratch = Path(args.scratch_root).resolve(); assert scratch.is_dir()
assert 1 <= args.max_workers <= 6
low_priority_single_core()

def repair_coordinate_binding_source(text, records):
    """Rewrite only checked binding proofs; preserve every numeric token."""
    changed = text
    for row in records:
        start = changed.index('namespace ' + row['namespace'] + '\n')
        end = changed.index('\nend ' + row['namespace'], start)
        body = changed[start:end]
        statement = 'theorem homRetained_binding : homRetained.map HomPoint.point = retained := by '
        assert body.count(statement + 'rfl') == 1
        changed = changed[:start] + body.replace(statement + 'rfl', statement + 't03_eq_refl') + changed[end:]
    changed = 'import ElevenSquare.Tasks.T03.KernelEqualityRefl\n' + changed
    assert re.findall(r'\b[0-9]+\b', text) == re.findall(r'\b[0-9]+\b', changed)
    return changed.encode('utf8')

def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()
accepted = json.loads((E / f'case{case}-coordinate-binding-pilot-accepted.json').read_text())
assert accepted['status'] == 'ALL_EXACT_FAILED_BINDING_PILOTS_ACCEPTED_BY_SUPPLIED_LEAN_CHECKER'
assert accepted['exact_coordinate_data_and_statement_unchanged']
diagnostic = json.loads((E / f'case{case}-coordinate-binding-diagnostic.json').read_text())
assert accepted['original_failed_group_source_sha256'] == diagnostic['failed_group_source_sha256']
assert set(accepted['target_axioms']) == {r['namespace'] + '.KernelBindingPilot.homRetained_binding'
                                       for r in diagnostic['records']}
assert all(set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
           for axioms in accepted['target_axioms'].values())
assert json.loads((E / 'equality-refl-benchmark.json').read_text())['kernel_negative_control_rejected']
old = f'forward-case{case}-assembly-task.json'
new = f'forward-case{case}-coordinate-binding-retry-assembly-task.json'
execution_name = args.failed_execution or ('extra-a-' + Path(old).stem + '.json')
assert Path(execution_name).name == execution_name
execution = json.loads((E / execution_name).read_text())
assert execution['exit_code'] == 1
record = E / f'case{case}-coordinate-binding-retry-publication.json'
archive = transport_root / ('.t03-runtime-sync-' + Path(old).stem + '.zip')
target = transport_root / ('.t03-runtime-sync-' + Path(new).stem + '.zip')
prepared = E / ('.prepared-' + new)
assert not record.exists() and not target.exists() and not prepared.exists() and not (E / new).exists()
assert all(j.get('case') != case and not j.get('task', '').startswith((f'library-case{case}-', f'forward-case{case}-')) for j in json.loads((E / 'unified-proof-pool-status.json').read_text())['active'].values())
old_sha = sha(archive)
assert old_sha == execution['transport_sha256']
module = diagnostic['failed_group']
name = 'project/' + module.replace('.', '/') + '.lean'
helper_name = 'project/ElevenSquare/Tasks/T03/KernelEqualityRefl.lean'
helper = (S / helper_name[8:]).read_bytes()
assert hashlib.sha256(helper).hexdigest() == '579aba76120723d18a2d3ee1464e136612cca06ef76f9547a67ae183b2c92200'
backup = scratch / (f'case{case}-binding-retry-' + datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
assert backup.resolve().parent == scratch.resolve() and not backup.exists()
backup.mkdir()
temporary = backup / 'retry-transport.zip'
with zipfile.ZipFile(archive) as z:
    manifest = json.loads(z.read('source-sync-manifest.json'))
    raw = z.read(name)
    assert hashlib.sha256(raw).hexdigest() == manifest[name] == diagnostic['failed_group_source_sha256']
    assert (S / name[8:]).read_bytes() == raw
    new_raw = repair_coordinate_binding_source(raw.decode('utf8'), diagnostic['records'])
    task_raw = z.read(old)
    assert task_raw == (E / old).read_bytes()
    assert hashlib.sha256(task_raw).hexdigest() == manifest[old]
    new_manifest = dict(manifest)
    del new_manifest[old]
    new_manifest[new] = hashlib.sha256(task_raw).hexdigest()
    new_manifest[name] = hashlib.sha256(new_raw).hexdigest()
    new_manifest[helper_name] = hashlib.sha256(helper).hexdigest()
    (backup / (Path(name).stem + '-before.lean')).write_bytes(raw)
    with zipfile.ZipFile(temporary, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=1) as out:
        for member in z.infolist():
            n = member.filename
            if n in ['source-sync-manifest.json', old, helper_name]:
                continue
            data = z.read(n)
            assert hashlib.sha256(data).hexdigest() == manifest[n]
            out.writestr(n, new_raw if n == name else data)
        out.writestr(new, task_raw)
        out.writestr(helper_name, helper)
        out.writestr('source-sync-manifest.json', json.dumps(new_manifest))
with zipfile.ZipFile(temporary) as z:
    assert len(z.namelist()) == len(set(z.namelist()))
    assert set(z.namelist()) == set(new_manifest) | {'source-sync-manifest.json'}
    for n, expected in new_manifest.items():
        assert hashlib.sha256(z.read(n)).hexdigest() == expected
assert sha(archive) == old_sha
with temporary.open('rb') as src, target.open('xb') as dst:
    while block := src.read(1024 * 1024):
        dst.write(block)
retry_sha = sha(target)
assert retry_sha == sha(temporary)
assert all(j.get('case') != case and not j.get('task', '').startswith((f'library-case{case}-', f'forward-case{case}-')) for j in json.loads((E / 'unified-proof-pool-status.json').read_text())['active'].values())
assert (S / name[8:]).read_bytes() == raw
(S / name[8:]).write_bytes(new_raw)
prepared.write_bytes(task_raw)
payload = dict(status='KERNEL_CHECKED_COORDINATE_BINDING_REPAIRS_PREPARED_FULL_CASE_AUDIT_PENDING',
    case=case, utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    retry_task=new, retry_archive_sha256=retry_sha, old_failed_archive_sha256=old_sha,
    changed_module=module, old_module_sha256=manifest[name], new_module_sha256=new_manifest[name],
    changed_proofs=len(diagnostic['records']), exact_certificate_target_unchanged=True,
    numeric_data_unchanged=True, previously_accepted_modules_unchanged=True,
    old_archive_preserved=True, backup_directory=str(backup), prepared_task=str(prepared),
    maximum_running_lean_checks=args.max_workers, full_case_and_final_audits_pending=True,
    lean_processes_started_by_preparation=0, original_targets=json.loads(task_raw)['axiom_targets'],
    actual_binding_pilot_record=f'case{case}-coordinate-binding-pilot-accepted.json')
record.write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps(payload), flush=True)
