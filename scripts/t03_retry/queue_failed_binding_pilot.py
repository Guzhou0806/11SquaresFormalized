"""Queue a small exact-data repair pilot through the existing six-slot pool."""
from pathlib import Path
import argparse, ctypes, datetime, hashlib, json, os, re, subprocess, sys

from retry_paths import kit_paths, low_priority_single_core
ap = argparse.ArgumentParser()
ap.add_argument('--case', type=int, required=True)
ap.add_argument('--kit', required=True)
ap.add_argument('--packer', required=True, help='Existing compatible kit source packer supporting TASK --named')
ap.add_argument('--max-workers', type=int, default=1)
args = ap.parse_args(); case = args.case
_, E, _ = kit_paths(args.kit)
S = E.parent / 'eleven-square-lean'
packer = Path(args.packer).resolve(); assert packer.is_file()
assert 1 <= args.max_workers <= 6
low_priority_single_core()
record = E / f'case{case}-coordinate-binding-pilot-queued.json'
assert not record.exists()
diagnostic = json.loads((E / f'case{case}-coordinate-binding-diagnostic.json').read_text())
assert diagnostic['case'] == case
assert diagnostic['status'] == 'EXACT_FRACTION_DIAGNOSTIC_NOT_A_LEAN_PROOF'
assert diagnostic['records'] and all(r['exact_points_equal_in_order'] for r in diagnostic['records'])
source = S / (diagnostic['failed_group'].replace('.', '/') + '.lean')
raw = source.read_bytes()
assert hashlib.sha256(raw).hexdigest() == diagnostic['failed_group_source_sha256']
text = raw.decode('utf8')
helper = S / 'ElevenSquare/Tasks/T03/KernelEqualityRefl.lean'
assert hashlib.sha256(helper.read_bytes()).hexdigest() == '579aba76120723d18a2d3ee1464e136612cca06ef76f9547a67ae183b2c92200'
negative = json.loads((E / 'equality-refl-benchmark.json').read_text())
assert negative['kernel_negative_control_rejected']
polygons = {}
bodies = []
targets = []
for row in diagnostic['records']:
    namespace = row['namespace']
    start = text.index('namespace ' + namespace + '\n')
    end = text.index('\nend ' + namespace, start)
    body = text[start:end]
    definitions = [re.search(r'^noncomputable def ' + name + r' : [^\n]+$', body, re.M)[0]
                   for name in ['retained', 'homRetained']]
    retained_namespace = row['retained_namespace']
    if retained_namespace not in polygons:
        marker = 'namespace ' + retained_namespace + '\n'
        for chunk in sorted(source.parent.glob('Chunk*.lean')):
            chunk_text = chunk.read_text(encoding='utf8')
            polygon_start = chunk_text.find(marker)
            if polygon_start < 0:
                continue
            vertices = re.search(r'^noncomputable def vertices : List QPoint := [^\n]+$',
                                 chunk_text[polygon_start:], re.M)[0]
            polygons[retained_namespace] = marker + vertices + '\nend ' + retained_namespace + '\n'
            break
        assert retained_namespace in polygons
    pilot_namespace = namespace + '.KernelBindingPilot'
    targets.append(pilot_namespace + '.homRetained_binding')
    bodies.append('namespace ' + pilot_namespace + '\nnoncomputable section\n' +
                  '\n'.join(definitions) +
                  '\ntheorem homRetained_binding : homRetained.map HomPoint.point = retained := by t03_eq_refl\n' +
                  'end\nend ' + pilot_namespace + '\n')
module = diagnostic['failed_group'].rsplit('.', 2)[0] + '.BindingRepairPilot'
pilot = S / (module.replace('.', '/') + '.lean')
assert not pilot.exists()
pilot_bytes = ('import ElevenSquare.Tasks.T03.HomogeneousPoints\n' +
               'import ElevenSquare.Tasks.T03.KernelEqualityRefl\n' +
               'set_option maxRecDepth 32768\nset_option maxHeartbeats 16000000\n' +
               '\n'.join(polygons.values()) + '\n'.join(bodies)).encode('utf8')
pilot.write_bytes(pilot_bytes)
task_name = f'library-case{case}-node999-000-task.json'
prepared = E / ('.prepared-' + task_name)
task_path = E / task_name
queue = E / f'library-case{case}-node999-queue.json'
assert not task_path.exists() and not prepared.exists() and not queue.exists()
task = dict(id='T03_exact_failed_coordinate_binding_repair_pilot', modules=[module], axiom_targets=targets)
# The packer only reads task bytes; no task is visible to the dispatcher yet.
task_path.write_text(json.dumps(task, indent=2) + '\n')
packed = subprocess.run([sys.executable, str(packer), task_name, '--named'],
                        check=True, capture_output=True, text=True)
metadata = json.loads(packed.stdout.strip())
prepared_task_sha = hashlib.sha256(task_path.read_bytes()).hexdigest()
payload = dict(status='TWO_EXACT_FAILED_BINDINGS_QUEUED_FOR_SUPPLIED_LEAN_CHECKER' if len(targets) == 2 else
                       'EXACT_FAILED_BINDINGS_QUEUED_FOR_SUPPLIED_LEAN_CHECKER',
               case=case, utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               original_failed_group=diagnostic['failed_group'],
               original_failed_group_source_sha256=diagnostic['failed_group_source_sha256'],
               pilot_module=module, pilot_source_sha256=hashlib.sha256(pilot_bytes).hexdigest(),
               task=task_name, task_sha256=prepared_task_sha, targets=targets,
               transport=metadata, production_case_sources_changed=False,
               exact_original_retained_homRetained_and_vertices_definitions_copied=True,
               maximum_parallel_lean_checks=args.max_workers, lean_processes_started_by_preparation=0,
               actual_pilot_audit_pending=True, full_case_audit_pending=True)
record.write_text(json.dumps(payload, indent=2) + '\n')
temporary = queue.with_suffix('.writing.json')
temporary.write_text(json.dumps(dict(status='EXACT_BINDING_PILOT_AWAITING_SUPPLIED_CHECKER',
    tasks=[dict(task=task_name, module=module, axiom_targets=targets, dependencies=[],
                remaining_dependency_path_groups=0)]), indent=2) + '\n')
temporary.replace(queue)
print(json.dumps(payload), flush=True)
