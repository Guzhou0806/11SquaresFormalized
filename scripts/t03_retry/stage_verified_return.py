"""Stage only the audited target closure and frozen baseline for the original exporter.

This intentionally refuses partial work. It never changes or replaces the supplied
exporter, checker, release metadata, or source contracts.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,re,shutil,sys

ap=argparse.ArgumentParser()
ap.add_argument('--handoff-log',type=Path,required=True)
ap.add_argument('--transport',type=Path,required=True)
ap.add_argument('--destination',type=Path,required=True)
ap.add_argument('--kit',required=True);ap.add_argument('--source-root',type=Path)
a=ap.parse_args()
assert sys.platform=='linux','Use WSL so the supplied protocol sees POSIX paths.'
from retry_paths import kit_paths
K,E,_=kit_paths(a.kit);P=a.source_root.resolve() if a.source_root else K/'eleven-square-lean'
task=json.loads((K/'TASK.json').read_text());release=json.loads((K/'RELEASE.json').read_text())
result=json.loads((E/'RESULT.json').read_text())
assert result['completed_case_certificates']==173,'Every complete case must pass first.'
log=a.handoff_log.read_text()
assert log.rstrip().endswith('PASS: target declarations have clean transitive axiom audits.')
matches=re.findall(r'Log: (/.*/handoff-HandoffAudit-[^/\s]+/lean.log)',log)
assert matches,'Expected the actual final supplied checker audit.'
audit=Path(matches[-1]);check=json.loads(audit.with_name('CHECK.json').read_text())
assert check['status']=='accepted' and check['exit_code']==0
output=audit.read_text()
execution=json.loads(a.handoff_log.with_suffix('.json').read_text())
assert execution['exit_code']==0
transport_digest=hashlib.sha256()
with a.transport.open('rb') as transport_file:
    while block:=transport_file.read(1024*1024):transport_digest.update(block)
assert execution['transport_sha256']==transport_digest.hexdigest()
report_text=(K/'REPORT.md').read_text()
assert 'PARTIAL' not in report_text.splitlines()[0], 'Rewrite the final report after the target audits.'
found={n:[v.strip() for v in ax.split(',') if v.strip()]
       for n,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output,re.S)}
found.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",output)})
assert set(task['axiom_targets'])<=found.keys()
assert all(set(found[n])<={'propext','Classical.choice','Quot.sound'} for n in task['axiom_targets'])

import zipfile
with zipfile.ZipFile(a.transport) as z:
    manifest=json.loads(z.read('source-sync-manifest.json'))
    archived_task=json.loads(z.read('TASK.json'))
assert archived_task==task

closure={}
def visit(module):
    rel='/'.join(module.split('.'))+'.lean'
    if rel in closure:return
    raw=(P/rel).read_bytes();digest=hashlib.sha256(raw).hexdigest()
    assert manifest.get('project/'+rel)==digest,('Source differs from final audit transport',rel)
    closure[rel]=digest
    for line in raw.decode('utf8').splitlines():
        if line.startswith('import '):
            for dep in line[7:].split('--')[0].split():
                if dep.startswith('ElevenSquare.'):visit(dep)
for module in task['modules']:visit(module)

sys.path.insert(0,str(K))
from protocol import owns,scan_source,scaffold
ownership=release['tasks'][task['id']]
files=set(release['source_manifest'])|set(closure)
dest=a.destination.resolve()
assert not dest.exists(),'Choose a fresh staging directory; existing work is preserved.'
assert not str(dest).startswith(str(P.resolve())+'/'),'Do not stage inside the source project.'
project=dest/'eleven-square-lean';evidence=dest/'agent-evidence'
project.mkdir(parents=True);evidence.mkdir()
records=[]
for rel in sorted(files):
    src=P/rel;raw=src.read_bytes();digest=hashlib.sha256(raw).hexdigest()
    baseline=release['source_manifest'].get(rel)
    if digest!=baseline:
        assert owns(ownership,rel),('Frozen source changed',rel)
        scan_source(raw,rel)
        assert len(raw)<16*1024*1024,('Oversized helper',rel)
        if rel in release['scaffolds']:
            assert scaffold(raw.decode())==release['scaffolds'][rel],('Changed contract',rel)
    target=project/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
    records.append(dict(path=rel,sha256=digest,bytes=len(raw),changed=digest!=baseline))

audit_source='\n'.join('import '+m for m in task['modules'])+'\n'+\
             '\n'.join('#print axioms '+n for n in task['axiom_targets'])+'\n'
(evidence/'Audit.lean').write_text(audit_source)
shutil.copyfile(audit,evidence/'audit.log')
shutil.copyfile(audit.with_name('CHECK.json'),evidence/'audit-CHECK.json')
shutil.copyfile(a.handoff_log,evidence/'final-handoff.log')
shutil.copyfile(a.handoff_log.with_suffix('.json'),evidence/'final-handoff-execution.json')
for name in ['TASK.json','RELEASE.json']:
    shutil.copyfile(K/name,evidence/name)
for name in ['RESULT.json','RESULT-before-final-target-verification.json','resumed-audit-snapshots.json','handoff-check-retries.json',
             'kernel-bool-pilot-comparison.json','kernel-bool-negative-control.log',
             'distance-shortcut-case1465-publication.json','distance-shortcut-incremental-transport.json',
             'distance-collision-feasibility.json','distance-collision-pilot.json',
             'distance-mathematical-shortcut.log','distance-geometry-alternative.log',
             'distance-geometry-baseline.log','distance-shortcut-case1465-pack.log',
             'InheritedAudit.lean','InheritedAudit.log','InheritedAudit-CHECK.json',
             'inherited-admissions.json','inherited-admissions-check.log',
             'case2047-log-collision-retry.json','case2122-output-write-retry.json',
             'runtime-log-collision-fix.json','runtime-efficiency-benchmark.json',
             'runtime-efficiency-application.json','runtime-efficiency-positive.log',
             'runtime-efficiency-kernel-negative.log','urgent-six-worker-transition.json',
             'cache-filesystem-benchmark.json','cache-lean-benchmark-retry01.json',
             'cache-lean-retry01-0-drvfs.log','cache-lean-retry01-1-ext4_image_on_d.log',
             'cache-lean-retry01-2-ext4_image_on_d.log','cache-lean-retry01-3-drvfs.log',
             'collision-bool-benchmark.json','collision-bool-baseline.log',
             'collision-bool-kernel_bool.log','collision-bool-queue-optimization.json',
             'nonblocking-optimization-dispatcher-transition.json',
             'collision-bool-preparation-efficiency-fix.json',
             'case1393-optimized-backfill-preparation.json',
             'parallel-backfill-inspection.json',
             'case1393-distance-opportunities.json','packed-compilation-benchmark.json',
             'case1646-packed-compilation-plan.json','case1646-packed-compilation-publication.json',
             'case1646-efficiency-resume.json','packed-import-compatibility.json','packed-import-compatibility.log',
             'case1646-packed-namespace-hold.json','case1646-packed-namespaced-publication.json',
             'case1646-packed-namespace-resume.json',
             'case1646-packed-namespaced-retry01-publication.json',
             'namespaced-packed-import-probe-preparation.json',
             'namespaced-packed-import-compatibility.json','namespaced-packed-import-compatibility.log',
             'packed-aware-dispatcher-transition.json','unused-diagnostic-queues-disabled.json',
             'case1393-packed-compilation-plan.json','case1393-packed-namespaced-publication.json',
             'case1393-critical-path-producer-transition.json','case1393-packed-chunk-audits-inspected.json',
             'case1311-packed-compilation-plan.json','case1311-packed-namespaced-publication.json',
             'case1311-packed-canonical-publication.json','case1311-queued-packing-status.json',
             'case1372-packed-compilation-plan.json','case1372-packed-namespaced-publication.json',
             'case1372-packed-canonical-publication.json','case1372-queued-packing-status.json',
             'equality-refl-benchmark.json','equality-refl-baseline.log','equality-refl-kernel_eq_refl.log',
             'equality-refl-false_rational_negative_control.log','case1393-equality-refl-publication.json',
             'case1393-equality-refl-producer-transition.json',
             'case1311-coordinate-binding-diagnostic.json',
             'case1311-coordinate-binding-lean-repair-probe.json',
             'case1311-coordinate-binding-lean-repair-probe-v2.json',
             'case1311-coordinate-binding-lean-repair-probe-v3.json',
             'case1311-binding-baseline.log','case1311-binding-kernel_eq_refl.log',
             'case1311-binding-v3-baseline.log','case1311-binding-v3-kernel_eq_refl.log',
             'case1311-coordinate-binding-retry-publication.json',
             'case1372-failed-group-external-reuse-hold.json',
             'worker-thread-default-fix.json','worker-global-metadata-default-fix.json','wand125-reuse-inspection.json',
             'external-certificate-reuse-priority.json','serial-preparation-external-reuse-hold.json',
             'external-reuse-continuation.json',
             'critical-path-dispatcher-transition.json','critical-path-dispatcher-transition-retry02.json',
             'dispatcher-history-refresh-efficiency.json',
             'binding-efficiency-continuation-20261001.json',
             'remaining-binding-efficiency-continuation-20261001.json','scratch-receipt-sharing-transition.json',
             'scratch-receipt-sharing-primary-transition.json',
             'native-source-sync-benchmark.json','native-source-sync-application.json',
             'equality-repair-efficiency-checkpoint-20261001.json',
             'efficiency-continuation-checkpoint-20261001.json','waiting-case-rotation-validation.json',
             'pending-shared-original-source-overlap.json',
             'case1465-packed-preparation-prechecks.json','case1465-efficiency-continuation.json',
             'case1464-efficiency-continuation.json','case1464-first-group-runtime-check.json',
             'case1464-first-group-runtime-check-precheck.json',
             'case1393-packed-canonical-publication.json','case1393-parallel-packed-status.json']:
    if (E/name).exists():shutil.copyfile(E/name,evidence/name)
for name in ['case1393-superseded-helper-retirement.json','case1393-superseded-queue-disabled.json']:
    if (E/name).exists():shutil.copyfile(E/name,evidence/name)
for publication in E.glob('case*-collision-bool-publication.json'):
    shutil.copyfile(publication,evidence/publication.name)
for pattern in ['case*-packed-compilation-plan.json','case*-packed-compilation-retry*-plan*.json',
                'all-pending-local-queues-checkpoint-*.json','fresh-local-fallback-preparation-status.json',
                'fresh-local-case*-*.log','case*-local-fallback-preparation-started.json',
                'case*-idle-rebalanced-local-publication.json','case*-external-reuse-queue-*.json',
                'case*-greedy-canonical-publication-before-local-retry.json',
                'case*-packed-namespaced*-publication.json',
                'case*-packed-canonical-publication.json','case*-queued-packing-status.json',
                'case*-packed-parallel-publication.json','case*-parallel-retry-transition.json',
                'case*-remaining-parallelism-plan.json','case*-remaining-parallel-source-publication.json',
                'case*-remaining-parallel-canonical-publication.json',
                'dependency-audit-timing-probe-*.json','homogeneous-fan-*.json',
                'ready-archive-prefilter-*.json',
                'case*-full-certificate-audit-checkpoint-*.json',
                '*-library-case1499-node996-homogeneous-fan-*.log',
                'case*-equality-refl*-publication.json','case*-equality-repair-producer-checkpoint*.json',
                'case*-parallel-packed-status-before-equality-repair*.json',
                'case*-private-packed-source-storage.json','*-task-source-sync.json',
                'wand125-reuse-inspection-*.json',
                'case*-parallel-packed-status.json','case*-packed-chunk-audits-inspected.json',
                'case*-coordinate-binding-diagnostic.json','case*-coordinate-binding-pilot-queued.json',
                'case*-coordinate-binding-pilot-accepted.json','case*-coordinate-binding-retry*-publication.json',
                'case*-external-reuse-hold-before-*.json','case*-local-check-resume.json',
                'case*-coordinate-binding-pilot-audit.log','case*-coordinate-binding-pilot-CHECK.json',
                'case*-coordinate-binding-pilot-source.lean',
                'critical-path-dispatcher-transition-retry*.json']:
    for publication in E.glob(pattern):shutil.copyfile(publication,evidence/publication.name)
for case in result['audited_case_certificates']:
    for suffix in ['.lean','.log','-CHECK.json']:
        name=case['audit']+suffix
        if (E/name).exists():shutil.copyfile(E/name,evidence/name)
provenance=dict(staged_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    task=task['id'],final_handoff_log=str(a.handoff_log),actual_audit_log=str(audit),
    final_transport=str(a.transport),final_transport_sha256=transport_digest.hexdigest(),
    target_axioms={n:found[n] for n in task['axiom_targets']},files=records)
(evidence/'staging-manifest.json').write_text(json.dumps(provenance,indent=2)+'\n')
(evidence/'commands.txt').write_text(
    'The final supplied checker command and resource limits are preserved in final-handoff.log and audit-CHECK.json.\n'
    'The actual pinned Lean compiler output is preserved verbatim in audit.log.\n'
    'Separate inherited admission audit: '+repr(json.loads((E/'inherited-admissions.json').read_text())['command'])+'\n'
    'Staging command: '+' '.join(sys.argv)+'\n'
    'Export with the original kit make_return.py against this staged project and evidence directory.\n')
shutil.copyfile(K/'REPORT.md',dest/'REPORT.md')
print(json.dumps(dict(status='STAGED_AUDITED_SOURCES_EXPORT_PENDING',destination=str(dest),
    reachable_lean_modules=len(closure),changed_sources=sum(r['changed'] for r in records))))
