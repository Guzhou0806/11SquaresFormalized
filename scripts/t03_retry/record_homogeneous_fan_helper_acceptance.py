"""Bind the actual integer-fan helper audit and the repaired 1465 group audit."""
from pathlib import Path
import datetime, hashlib, json, re

import argparse
from retry_paths import kit_paths,metadata_path
ap=argparse.ArgumentParser()
ap.add_argument('--kit',required=True)
ap.add_argument('--source-root',type=Path)
ap.add_argument('--helper-prefix',default='library-b')
ap.add_argument('--include-group105',action='store_true')
ap.add_argument('--group-prefix',default='helper')
ap.add_argument('--reported-accepted-cases',type=int,required=True)
ap.add_argument('--max-workers',type=int,default=1)
ap.add_argument('--output',default='homogeneous-fan-helper-accepted.json')
a=ap.parse_args();K,E,transport_root=kit_paths(a.kit)
S=a.source_root.resolve() if a.source_root else K/'eleven-square-lean'
assert 0<=a.reported_accepted_cases<=173
assert 1<=a.max_workers<=6
assert Path(a.output).name==a.output and a.output.endswith('.json')
def win(s):return metadata_path(s)

def collect(prefix, task):
    wrapper = E / (prefix + '-' + Path(task).stem + '.log')
    execution_path = wrapper.with_suffix('.json')
    execution = json.loads(execution_path.read_text())
    assert execution['exit_code'] == 0 and execution['task'] == task
    text = wrapper.read_text(encoding='utf8')
    assert text.rstrip().endswith('PASS: target declarations have clean transitive axiom audits.')
    audit_paths = re.findall(r'^Log: (\S+/handoff-HandoffAudit-\S+/lean\.log)$', text, re.M)
    assert len(audit_paths) == 1
    audit_path = win(audit_paths[0])
    check_path = audit_path.with_name('CHECK.json')
    check_bytes = check_path.read_bytes()
    check = json.loads(check_bytes)
    assert check['status'] == 'accepted' and check['exit_code'] == 0
    raw = audit_path.read_bytes()
    audited = {n: [a.strip() for a in v.split(',') if a.strip()] for n, v in
               re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", raw.decode(), re.S)}
    targets = json.loads((E / task).read_text())['axiom_targets']
    assert set(targets) == set(audited)
    assert all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in audited.values())
    return dict(task=task, actual_audit=str(audit_path), actual_CHECK=str(check_path),
                audit_sha256=hashlib.sha256(raw).hexdigest(),
                CHECK_sha256=hashlib.sha256(check_bytes).hexdigest(),
                audit_seconds=check['elapsed_seconds'], target_axioms=audited,
                transport_sha256=execution['transport_sha256'])

helper = collect(a.helper_prefix, 'library-case1499-node996-homogeneous-fan-helper-probe-task.json')
prep = json.loads((E / 'homogeneous-fan-helper-probe-preparation.json').read_text())
assert helper['transport_sha256'] == prep['transport_sha256']
source = S / 'ElevenSquare/Tasks/T03/HomogeneousPolygonFan.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == prep['helper_sha256']
group105 = collect(a.group_prefix, 'library-case1465-node998-105-equality-retry03-task.json') if a.include_group105 else None
record = E / a.output
assert not record.exists()
p = dict(status='ABSTRACT_INTEGER_FAN_BRIDGE_ACTUALLY_AUDITED_COMPARISON_PENDING',
         utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         helper=helper, helper_source_sha256=prep['helper_sha256'], repaired1465group105=group105,
         exact_original_rational_boolean_claim_preserved=True,
         comparison_queued='homogeneous-fan-comparison-preparation.json',
         concrete_speedup_and_case_application_pending=True,
         reported_completed_case_certificates=a.reported_accepted_cases, maximum_global_compiler_checks=a.max_workers,
         integration_zip_created=False)
record.write_text(json.dumps(p, indent=2) + '\n')
print(json.dumps({k: v for k, v in p.items() if k not in ['helper', 'repaired1465group105']}))
