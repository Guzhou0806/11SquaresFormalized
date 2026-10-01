"""Reuse every accepted prefix byte and regroup only the idle failed remainder.

Copies exact already namespaced declaration bodies, preserving their original
source bindings, all statements and numeric tokens. Replaces only ordinary
reflexivity construction. All new groups and the full original target require
actual supplied-checker kernel checks and transitive axiom audits.
"""
from pathlib import Path
import argparse, ctypes, datetime, hashlib, json, os, re, shutil, subprocess, zipfile
from retry_paths import kit_paths, low_priority_single_core
ap = argparse.ArgumentParser()
ap.add_argument('--case', type=int, required=True)
ap.add_argument('--kit',required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--scratch-root',required=True)
ap.add_argument('--max-workers',type=int,default=1)
ap.add_argument('--source-root',type=Path)
ap.add_argument('--wsl-distro',default='Ubuntu')
a=ap.parse_args();case=a.case
K,E,transport_root=kit_paths(a.kit,a.transport_dir)
scratch=Path(a.scratch_root).resolve();assert scratch.is_dir()
assert 1<=a.max_workers<=6
low_priority_single_core()
S=a.source_root.resolve() if a.source_root else K/'eleven-square-lean'
assert case == 1499
def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        while block := f.read(1024*1024):
            h.update(block)
    return h.hexdigest()
plan_path = E / f'case{case}-remaining-parallelism-plan.json'
plan = json.loads(plan_path.read_text())
assert plan['status'] == 'EXACT_REMAINING_PARALLEL_SOURCE_PLAN_NO_PROOF_CHANGE_OR_CHECK'
assert plan['preserved_prefix_groups'] == 26
assert not any(j.get('case') == case for j in json.loads((E / 'unified-proof-pool-status.json').read_text())['active'].values())
assert case not in {r['case'] for r in json.loads((E / 'RESULT.json').read_text())['audited_case_certificates']}
old_prep = json.loads((E / plan['original_preparation_file']).read_text())
original_plan = json.loads((E / plan['original_plan_file']).read_text())
old_master = transport_root / ('.t03-runtime-sync-' + Path(plan['old_task']).stem + '.zip')
assert sha(old_master) == plan['old_transport_sha256']
new_task_name = f'forward-case{case}-parallel-retry01-assembly-task.json'
new_master = transport_root / ('.t03-runtime-sync-' + Path(new_task_name).stem + '.zip')
prep_path = E / f'case{case}-remaining-parallel-source-publication.json'
pub_path = E / f'case{case}-remaining-parallel-canonical-publication.json'
guard = E / f'.collision-bool-preparing-case{case}.json'
assert not any(q.exists() for q in [prep_path, pub_path, guard, new_master, E / new_task_name])
prefix = old_prep['root_module'].rsplit('.PackedNamespaced.', 1)[0] + '.PackedRemainingRetry01'
logical = S / prefix.replace('.', '/')
physical = scratch/'private-packed-sources'/f'case{case}'/'PackedRemainingRetry01'
assert not logical.exists() and not physical.exists()
assert logical.parent.resolve().is_relative_to((S / 'ElevenSquare/Tasks/T03').resolve())
assert physical.resolve().is_relative_to(scratch)
physical.mkdir(parents=True)
quote = lambda p: "'" + str(p).replace("'", "''") + "'"
subprocess.run(['powershell.exe', '-NoProfile', '-Command', 'New-Item -ItemType Junction -Path ' + quote(logical) + ' -Target ' + quote(physical) + ' -ErrorAction Stop | Out-Null'], check=True)
assert logical.resolve() == physical.resolve()
def mounted_path(path):
    value=str(path.absolute()).replace(chr(92),'/')
    match=re.fullmatch(r'([A-Za-z]):/(.*)',value)
    assert match, 'Supply a drive-based logical source path'
    return '/mnt/'+match[1].lower()+'/'+match[2]
probe = logical / '.storage-probe.txt'
probe.write_bytes(b'T03 exact remaining source storage\n')
subprocess.run(['wsl.exe','-d',a.wsl_distro,'--','python3','-c',
    'from pathlib import Path; import sys; assert Path(sys.argv[1]).read_bytes()==b"T03 exact remaining source storage\\n"',
    mounted_path(probe)], check=True)
probe.unlink()
backup = scratch / (f'case{case}-remaining-parallel-' + datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
assert not backup.exists()
backup.mkdir()
(backup / plan_path.name).write_bytes(plan_path.read_bytes())
shutil.copyfile(old_master, backup / old_master.name)
assert sha(backup / old_master.name) == plan['old_transport_sha256']
marker = re.compile(r'^-- Original source: ([A-Za-z_0-9.]+); SHA256 ([a-f0-9]{64})\nsection\n', re.M)
pattern = re.compile(r'(?<=by )rfl\b|(?<=<;> )rfl\b')
blocks = {}
changed = []
group_bytes = {}
group_imports = {}
mapping = {m: prefix+f'.Chunk{i:03d}' for i,g in enumerate(plan['remaining_groups']) for m in g}
old_mapping = plan['exact_old_group_bindings']
mapping.update({m:g for m,g in old_mapping.items() if int(g.rsplit('Chunk',1)[1]) < plan['preserved_prefix_groups']})
original_bindings = {r['module']:r['source_sha256'] for r in old_prep['packed_body_bindings']}
body_bindings = []
with zipfile.ZipFile(old_master) as old:
    manifest = json.loads(old.read('source-sync-manifest.json'))
    task = json.loads(old.read(plan['old_task']))
    bridge = old_prep['exact_original_target_bridge']
    for group_number in range(old_prep['groups']):
        module = old_prep['root_module'].rsplit('.',1)[0] + f'.Chunk{group_number:03d}'
        member = 'project/' + module.replace('.', '/') + '.lean'
        raw = old.read(member)
        assert hashlib.sha256(raw).hexdigest() == manifest[member]
        assert (S / member[8:]).read_bytes() == raw
        text = raw.decode('utf8')
        if module == old_prep['root_module']:
            assert text.endswith(bridge)
            text = text[:-len(bridge)]
        matches = list(marker.finditer(text))
        assert matches
        header = text[:matches[0].start()]
        assert not re.sub(r'^import [^\n]*\n', '', header, flags=re.M).strip()
        expected_modules = [r['module'] for r in old_prep['packed_body_bindings'] if r['group'] == module]
        assert [m[1] for m in matches] == expected_modules
        for index,m in enumerate(matches):
            assert m[2] == original_bindings[m[1]] and old_mapping[m[1]] == module
            block = text[m.start():matches[index+1].start() if index+1 < len(matches) else len(text)]
            assert block.endswith('\nend\n\n') and m[1] not in blocks
            blocks[m[1]] = block
    assert set(blocks) == set(old_mapping)
    external = {d for deps in original_plan['chunk_imports'].values() for d in deps
                if not (d == 'ElevenSquare' or d.startswith('ElevenSquare.'))}
    for index, group in enumerate(plan['remaining_groups']):
        module = prefix + f'.Chunk{index:03d}'
        dependencies = set(external) | {'ElevenSquare.Tasks.T03.KernelBoolRefl', 'ElevenSquare.Tasks.T03.KernelEqualityRefl'}
        parts = []
        for original_module in group:
            block = blocks[original_module]
            new_block, count = pattern.subn('t03_eq_refl', block)
            assert re.findall(r'\b[0-9]+\b', block) == re.findall(r'\b[0-9]+\b', new_block)
            if count:
                changed.append(dict(original_module=original_module, equalities=count,
                                    old_block_sha256=hashlib.sha256(block.encode()).hexdigest(),
                                    new_block_sha256=hashlib.sha256(new_block.encode()).hexdigest()))
            parts.append(new_block)
            body_bindings.append(dict(module=original_module, source_sha256=original_bindings[original_module],
                                      old_group=old_mapping[original_module], group=module))
            dependencies.update(mapping.get(d,d) for d in original_plan['graph'][original_module] if mapping.get(d,d) != module)
        group_imports[module] = sorted(dependencies)
        group_bytes[module] = ('\n'.join('import '+d for d in group_imports[module])+'\n\n'+''.join(parts)).encode()
    root = mapping[original_plan['original_task']['modules'][0]]
    group_bytes[root] += bridge.encode()
    task['modules'] = [root]
    assert task['axiom_targets'] == old_prep['axiom_targets']
    task_raw = (json.dumps(task, indent=2)+'\n').encode()
    selected = set()
    visiting = set()
    def source(module):
        if module in group_bytes:
            return group_bytes[module]
        member = 'project/' + module.replace('.', '/') + '.lean'
        raw = old.read(member)
        assert hashlib.sha256(raw).hexdigest() == manifest[member]
        return raw
    def visit(module):
        if module in selected:
            return
        assert module not in visiting
        visiting.add(module)
        raw = source(module)
        for line in raw.decode().splitlines():
            if line.startswith('import '):
                for dep in line[7:].split('--')[0].split():
                    if dep == 'ElevenSquare' or dep.startswith('ElevenSquare.'):
                        visit(dep)
        visiting.remove(module)
        selected.add(module)
    visit(root)
    assert set(group_bytes) <= selected
    old_groups_in_closure = {m for m in selected if '.PackedNamespaced.' in m}
    assert old_groups_in_closure == {g for m,g in old_mapping.items() if m not in {r['module'] for r in body_bindings}}
    for module, raw in group_bytes.items():
        assert len(raw) < 16*1024*1024
        path = S / (module.replace('.', '/')+'.lean')
        assert not path.exists()
        path.write_bytes(raw)
    temporary = backup / 'new-master.zip'
    new_manifest = {}
    extras = ['TASK.json'] + ['project/'+n for n in ['lakefile.lean','lake-manifest.json','lean-toolchain','scripts/lake.sh','scripts/check_handoff.py','scripts/lean_small_check.py','verification/LOW_RESOURCE_MODE.json']]
    with zipfile.ZipFile(temporary, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=1) as out:
        for module in sorted(selected):
            member = 'project/'+module.replace('.', '/')+'.lean'
            raw = source(module)
            assert len(raw) < 16*1024*1024
            new_manifest[member] = hashlib.sha256(raw).hexdigest()
            out.writestr(member, raw)
        for member in extras:
            raw = old.read(member)
            assert hashlib.sha256(raw).hexdigest() == manifest[member]
            new_manifest[member] = manifest[member]
            out.writestr(member, raw)
        new_manifest[new_task_name] = hashlib.sha256(task_raw).hexdigest()
        out.writestr(new_task_name, task_raw)
        out.writestr('source-sync-manifest.json', json.dumps(new_manifest))
with zipfile.ZipFile(temporary) as check:
    assert len(check.namelist()) == len(set(check.namelist()))
    assert set(check.namelist()) == set(new_manifest) | {'source-sync-manifest.json'}
    for member, expected in new_manifest.items():
        assert hashlib.sha256(check.read(member)).hexdigest() == expected
assert sha(old_master) == plan['old_transport_sha256']
shutil.copyfile(temporary, new_master)
assert sha(new_master) == sha(temporary)
p = dict(status='PACKED_CASE_PREPARED_NOT_LEAN_CHECKED_OR_DISPATCHED', case=case,
         utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), task=new_task_name,
         archive=str(new_master), archive_sha256=sha(new_master), root_module=root,
         group_module_prefix=prefix+'.', groups=len(group_bytes), axiom_targets=task['axiom_targets'],
         original_modules_grouped=len(body_bindings), packed_body_bindings=body_bindings,
         source_manifest=new_manifest, private_namespaces_renamed=False,
         preserved_old_namespace_suffix=old_prep['namespace_suffix'],
         numeric_tokens_unchanged=True, all_old_accepted_prefix_bytes_unchanged=True,
         preserved_prefix_groups=plan['preserved_prefix_groups'],
         original_exact_target_bridge_unchanged=True, changed_proof_blocks=changed,
         changed_equality_proof_constructions=sum(r['equalities'] for r in changed),
         prior_failed_transport_sha256=plan['old_transport_sha256'],
         backup_directory=str(backup), logical_owned_module_directory=str(logical), physical_directory=str(physical),
         maximum_global_compiler_checks=a.max_workers, full_case_and_final_target_audits_pending=True,
         lean_processes_started=0)
prep_path.write_text(json.dumps(p, indent=2)+'\n')
guard.write_text(json.dumps(dict(status='EXACT_GROUPED_RETRY_HELD_FOR_PARALLEL_DEPENDENCY_AUDITS',
    case=case, required_dependency_groups=len(group_bytes), preserved_prefix_groups=plan['preserved_prefix_groups'],
    exact_original_target=task['axiom_targets'], source_archive_sha256=p['archive_sha256'],
    maximum_global_compiler_checks=a.max_workers, full_case_and_final_audits_pending=True), indent=2)+'\n')
(E / new_task_name).write_bytes(task_raw)
pub_path.write_text(json.dumps(dict(status='EXACT_REMAINING_PARALLEL_CASE_QUEUED_FULL_AUDIT_PENDING',
    case=case, task=new_task_name, root_module=root, groups=len(group_bytes), grouped_archive_sha256=p['archive_sha256'],
    original_target=task['axiom_targets'], preserved_prefix_groups=plan['preserved_prefix_groups'],
    full_case_guard_retained_for_parallel_dependency_audits=True, running_proof_workers_unchanged=True), indent=2)+'\n')
print(json.dumps({k:v for k,v in p.items() if k not in ['packed_body_bindings','source_manifest','changed_proof_blocks']}), flush=True)
