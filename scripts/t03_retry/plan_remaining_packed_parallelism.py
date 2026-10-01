"""Read-only exact dependency plan after a real failed packed-case check."""
from pathlib import Path
import argparse, collections, ctypes, datetime, hashlib, json, os, re, zipfile
from retry_paths import kit_paths, low_priority_single_core, metadata_path
ap = argparse.ArgumentParser()
ap.add_argument('--case', type=int, required=True)
ap.add_argument('--prefix', type=int, required=True)
ap.add_argument('--worker', required=True)
ap.add_argument('--kit',required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--scratch-root',required=True)
ap.add_argument('--max-workers',type=int,default=1)
a = ap.parse_args()
K,E,transport_root=kit_paths(a.kit,a.transport_dir)
scratch=Path(a.scratch_root).resolve();assert scratch.is_dir()
assert 1<=a.max_workers<=6
low_priority_single_core()
case = a.case
assert a.prefix > 0
def win(value):
    return metadata_path(value)
prep_path = E / f'case{case}-packed-namespaced-publication.json'
prep = json.loads(prep_path.read_text())
plan_path = E / f'case{case}-packed-compilation-plan.json'
original_plan = json.loads(plan_path.read_text())
task_name = prep['task']
wrapper = (E / (a.worker + '-' + Path(task_name).stem + '.log')).read_text(encoding='utf8')
execution_path = E / (a.worker + '-' + Path(task_name).stem + '.json')
execution = json.loads(execution_path.read_text())
assert execution['exit_code'] == 1 and execution['task'] == task_name
assert not any(j.get('case') == case for j in json.loads((E / 'unified-proof-pool-status.json').read_text())['active'].values())
checks = []
for number in range(a.prefix):
    logs = re.findall(r'^Log: (\S+/handoff-Chunk' + f'{number:03d}' + r'-\S+/lean\.log)$', wrapper, re.M)
    assert len(logs) == 1
    check_path = win(logs[0]).with_name('CHECK.json')
    raw = check_path.read_bytes()
    check = json.loads(raw)
    assert check['status'] == 'accepted' and check['exit_code'] == 0
    assert check['source'].endswith(f'Case{case}/PackedNamespaced/Chunk{number:03d}.lean')
    checks.append(dict(group=number, actual_CHECK=str(check_path), CHECK_sha256=hashlib.sha256(raw).hexdigest()))
failed_logs = re.findall(r'^Log: (\S+/handoff-Chunk' + f'{a.prefix:03d}' + r'-\S+/lean\.log)$', wrapper, re.M)
assert len(failed_logs) == 1
failed_log = win(failed_logs[0])
failed_raw = failed_log.read_bytes()
failed_check = json.loads(failed_log.with_name('CHECK.json').read_text())
assert failed_check['exit_code'] == 1
errors = [line for line in failed_raw.decode().splitlines() if ': error:' in line]
assert errors and all('The rfl tactic failed' in line or 'unsolved goals' in line for line in errors)
bindings = prep['packed_body_bindings']
assert {r['module'] for r in bindings} == {m for g in original_plan['groups'] for m in g}
old_group = {r['module']: r['group'] for r in bindings}
preserved = {m for m,g in old_group.items() if int(g.rsplit('Chunk',1)[1]) < a.prefix}
remaining = set(old_group) - preserved
depth = {}
levels = collections.defaultdict(list)
for module, dependencies in original_plan['graph'].items():
    if module in remaining:
        depth[module] = 1 + max((depth[d] for d in dependencies if d in remaining), default=0)
        levels[depth[module]].append(module)
    elif module in preserved:
        assert not set(dependencies) & remaining
assert set(depth) == remaining
groups = []
master = transport_root / ('.t03-runtime-sync-' + Path(task_name).stem + '.zip')
hsh = hashlib.sha256()
with master.open('rb') as f:
    while block := f.read(1024 * 1024):
        hsh.update(block)
assert hsh.hexdigest() == execution['transport_sha256']
original_archive = win(json.loads((E / f'case{case}-packed-canonical-publication.json').read_text())['original_archive_backup'])
with zipfile.ZipFile(original_archive) as z:
    for level in sorted(levels):
        group = []
        size = 0
        for module in levels[level]:
            n = z.getinfo('project/' + module.replace('.', '/') + '.lean').file_size
            if group and (len(group) >= 64 or size+n > 8*1024*1024):
                groups.append(group)
                group = []
                size = 0
            group.append(module)
            size += n
        if group:
            groups.append(group)
p = dict(status='EXACT_REMAINING_PARALLEL_SOURCE_PLAN_NO_PROOF_CHANGE_OR_CHECK', case=case,
         utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         preserved_prefix_groups=a.prefix, preserved_original_modules=len(preserved),
         remaining_original_modules=len(remaining), remaining_depth_groups=len(groups),
         remaining_dependency_depths=len(levels), maximum_parallel_module_width=max(map(len,levels.values())),
         current_serial_remaining_groups=prep['groups']-a.prefix,
         old_task=task_name, old_transport_sha256=execution['transport_sha256'],
         original_source_archive=str(original_archive),
         preserved_actual_compiler_checks=checks, actual_failed_log=str(failed_log),
         actual_failed_log_sha256=hashlib.sha256(failed_raw).hexdigest(), actual_failed_CHECK=failed_check,
         original_plan_file=plan_path.name, original_preparation_file=prep_path.name,
         exact_old_group_bindings=old_group, remaining_groups=groups,
         sources_changed=[], lean_processes_started=0, full_case_audit_pending=True)
record = E / f'case{case}-remaining-parallelism-plan.json'
assert not record.exists()
record.write_text(json.dumps(p, indent=2) + '\n')
print(json.dumps({k:v for k,v in p.items() if k not in ['preserved_actual_compiler_checks','exact_old_group_bindings','remaining_groups','actual_failed_CHECK']}), flush=True)
