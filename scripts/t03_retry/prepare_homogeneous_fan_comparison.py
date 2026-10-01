"""Compare identical original polygon claims through rational and integer checks.

Only queued after the abstract bridge has passed the unchanged handoff checker.
Both bounded modules retain identical original points, planes, and factors.
"""
from pathlib import Path
from fractions import Fraction
import ast, ctypes, datetime, hashlib, json, math, os, re, shutil, zipfile

import argparse
from retry_paths import kit_paths,low_priority_single_core,metadata_path
ap=argparse.ArgumentParser()
ap.add_argument('--kit',required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--scratch-root',required=True)
ap.add_argument('--source-root',type=Path)
ap.add_argument('--max-workers',type=int,default=1)
ap.add_argument('--polygon-source',type=Path,required=True)
a=ap.parse_args()
K,E,transport_root=kit_paths(a.kit,a.transport_dir)
S=a.source_root.resolve() if a.source_root else K/'eleven-square-lean'
scratch=Path(a.scratch_root).resolve();assert scratch.is_dir()
assert 1<=a.max_workers<=6
low_priority_single_core()
helper_task = 'library-case1499-node996-homogeneous-fan-helper-probe-task.json'
prefixes = ['primary', 'independent', 'helper', 'extra-a', 'library-b', 'library-c']
accepted = []
for prefix in prefixes:
    result = E / (prefix + '-' + Path(helper_task).stem + '.json')
    log = result.with_suffix('.log')
    if result.exists() and json.loads(result.read_text())['exit_code'] == 0:
        assert log.read_text().rstrip().endswith('PASS: target declarations have clean transitive axiom audits.')
        accepted.append(json.loads(result.read_text()))
assert len(accepted) == 1, 'Abstract arithmetic bridge must actually pass before a comparison is queued'
source = a.polygon_source.resolve()
blocks = source.read_text(encoding='utf8').split('-- Original source: ')[1:]
block = next(b for b in blocks if 'polygonFanCheck shapeVertices shapeEdges' in b)
lines = block.splitlines()
defs = {n: next(l for l in lines if re.match(r'(?:noncomputable )?def ' + n + r'\b', l))
        for n in ['shapeVertices', 'shapePlanes', 'shapeFactors']}

def literal(node):
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return Fraction(node.value)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -literal(node.operand)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        return literal(node.left) / literal(node.right)
    if isinstance(node, (ast.List, ast.Tuple)):
        return [literal(n) for n in node.elts]
    raise AssertionError('Unexpected exact rational literal: ' + ast.dump(node))

vertices = literal(ast.parse(defs['shapeVertices'].split(' := ', 1)[1], mode='eval').body)
factors = literal(ast.parse(defs['shapeFactors'].split(' := ', 1)[1], mode='eval').body)
plane_text = defs['shapePlanes'].split(' := ', 1)[1]
planes = [tuple(map(int, x.split(','))) for x in re.findall(r'⟨([^⟩]*)⟩', plane_text)]
assert len(vertices) == len(planes) == len(factors) >= 3
points = []
for x, y in vertices:
    d = math.lcm(x.denominator, y.denominator)
    points.append((int(x * d), int(y * d), d))
for i, (p, plane, factor) in enumerate(zip(points, planes, factors)):
    q = points[(i + 1) % len(points)]
    ax, ay, ad = p
    bx, by, bd = q
    fn, fd = factor.numerator, factor.denominator
    assert fn > 0 and fd > 0 and ad > 0 and bd > 0
    assert plane[0] * fd * ad * bd == fn * (by * ad - ay * bd)
    assert plane[1] * fd * ad * bd == fn * (ax * bd - bx * ad)
    assert plane[2] * fd * ad * bd == fn * (by * ax - bx * ay)
for i in range(1, len(points) - 1):
    ax, ay, ad = points[0]
    bx, by, bd = points[i]
    cx, cy, cd = points[i + 1]
    assert ax * (by * cd - cy * bd) - ay * (bx * cd - cx * bd) + ad * (bx * cy - by * cx) > 0
common = '\n'.join(defs[n] for n in ['shapeVertices', 'shapePlanes', 'shapeFactors']) + '\n'
common += 'noncomputable def shapeEdges : List EdgePlane := List.zipWith (fun l f => ⟨l,f⟩) shapePlanes shapeFactors\n'
imports = ('import ElevenSquare.Tasks.T03.HomogeneousPolygonFan\n'
           'import ElevenSquare.Tasks.T03.KernelBoolRefl\n'
           'import ElevenSquare.Tasks.T03.KernelEqualityRefl\n\n')
modules = []
targets = []
for label in ['Rational', 'Integer']:
    module = 'ElevenSquare.Tasks.T03.HomogeneousFanComparison' + label
    namespace = 'ElevenSquare.Pending.T03.HomogeneousFanComparison' + label
    text = imports + 'namespace ' + namespace + '\nnoncomputable section\n'
    text += 'set_option maxRecDepth 32768\nset_option maxHeartbeats 16000000\n' + common
    if label == 'Rational':
        text += 'theorem shapeChecked : polygonFanCheck shapeVertices shapeEdges = true := by t03_bool_refl\n'
    else:
        text += 'def homVertices : List HomPoint := [' + ','.join('⟨' + ','.join(map(str, p)) + '⟩' for p in points) + ']\n'
        text += 'def homEdges : List HomEdgeCertificate := [' + ','.join('⟨' + str(f.numerator) + ',' + str(f.denominator) + '⟩' for f in factors) + ']\n'
        text += ('theorem homBinding : homVertices.map HomPoint.point = shapeVertices := by t03_eq_refl\n'
                 'theorem integerChecked : homogeneousPolygonFanCheck homVertices shapeEdges homEdges = true := by t03_bool_refl\n'
                 'theorem shapeChecked : polygonFanCheck shapeVertices shapeEdges = true := by\n'
                 '  rw [← homBinding]\n'
                 '  exact homogeneousPolygonFanCheck_sound homVertices shapeEdges homEdges integerChecked\n'
                 'theorem zeroDenominatorRejected : homogeneousPolygonFanCheck\n'
                 '    [⟨0,0,0⟩,⟨1,0,1⟩,⟨0,1,1⟩] [] [] = false := by t03_eq_refl\n')
        targets.append(namespace + '.zeroDenominatorRejected')
    text += 'end\nend ' + namespace + '\n'
    path = S / (module.replace('.', '/') + '.lean')
    assert not path.exists()
    path.write_text(text, encoding='utf8')
    modules.append(module)
    targets.append(namespace + '.shapeChecked')
task_name = 'library-case1499-node996-homogeneous-fan-comparison-task.json'
queue = E / 'library-case1499-node996-comparison-queue.json'
assert not queue.exists() and not (E / task_name).exists()
task = json.loads((E / helper_task).read_text())
task.update(id='T03_IDENTICAL_POLYGON_INTEGER_FAN_COMPARISON_NOT_CASE_EVIDENCE', modules=modules,
            axiom_targets=targets, check_scope='One identical 56-vertex polygon comparison; no full case acceptance.')
task_raw = (json.dumps(task, indent=2) + '\n').encode()
members = {}
visiting = set()

def visit(m):
    n = 'project/' + m.replace('.', '/') + '.lean'
    if n in members:
        return
    assert m not in visiting
    visiting.add(m)
    raw = (S / n[8:]).read_bytes()
    for line in raw.decode().splitlines():
        if line.startswith('import '):
            for dep in line[7:].split('--')[0].split():
                if dep == 'ElevenSquare' or dep.startswith('ElevenSquare.'):
                    visit(dep)
    members[n] = raw
    visiting.remove(m)

for m in modules:
    visit(m)
for n in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain',
          'scripts/check_handoff.py', 'scripts/lean_small_check.py', 'scripts/lake.sh']:
    members['project/' + n] = (S / n).read_bytes()
members[task_name] = task_raw
manifest = {n: hashlib.sha256(raw).hexdigest() for n, raw in members.items()}
name = '.t03-runtime-sync-' + Path(task_name).stem + '.zip'
temporary = scratch / name
target = transport_root / name
assert not temporary.exists() and not target.exists()
with zipfile.ZipFile(temporary, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=1) as out:
    for n, raw in members.items():
        out.writestr(n, raw)
    out.writestr('source-sync-manifest.json', json.dumps(manifest))
with zipfile.ZipFile(temporary) as checked:
    assert len(checked.namelist()) == len(set(checked.namelist()))
    for n, expected in manifest.items():
        assert hashlib.sha256(checked.read(n)).hexdigest() == expected
shutil.copyfile(temporary, target)
digest = hashlib.sha256(temporary.read_bytes()).hexdigest()
assert hashlib.sha256(target.read_bytes()).hexdigest() == digest
(E / task_name).write_bytes(task_raw)
queue.write_text(json.dumps(dict(status='IDENTICAL_POLYGON_COMPARISON_NOT_CASE_EVIDENCE', tasks=[dict(
    task=task_name, module=modules[-1], axiom_targets=targets, dependencies=[],
    remaining_dependency_path_groups=1000)]), indent=2) + '\n')
record = dict(status='IDENTICAL_ORIGINAL_POLYGON_COMPARISON_QUEUED_TIMING_PENDING',
              utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), task=task_name,
              source_file=str(source), source_file_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
              original_source_binding=lines[0], vertices=len(vertices),
              exact_original_definition_bytes_identical_between_both_modules=True,
              original_definition_sha256=hashlib.sha256(common.encode()).hexdigest(),
              helper_execution=accepted[0], transport_sha256=digest,
              sources_of_running_proof_jobs_changed=False, maximum_global_compiler_checks=a.max_workers,
              case_acceptance_count_changed=False, targets=targets, modules=modules)
(E / 'homogeneous-fan-comparison-preparation.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record), flush=True)
