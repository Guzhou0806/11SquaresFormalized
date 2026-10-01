"""Measure source-ready prefiltering without running or accepting any proof."""
from pathlib import Path
import argparse,datetime, json, os, time

ap=argparse.ArgumentParser()
ap.add_argument('--kit',required=True);ap.add_argument('--transport-dir');ap.add_argument('--output',required=True)
from retry_paths import kit_paths,low_priority_single_core
a=ap.parse_args();K,E,transport_root=kit_paths(a.kit,a.transport_dir)
assert Path(a.output).name==a.output and a.output.endswith('.json')
low_priority_single_core()
pool = json.loads((E / 'unified-proof-pool-status.json').read_text())
attempted = {r['task'] for r in pool['events'] if r.get('status') == 'CHECK_STARTED'}
done = {r['case'] for r in json.loads((E / 'RESULT.json').read_text())['audited_case_certificates']}
rows = []
for queue in sorted(E.glob('library-case*-node*-queue.json')):
    case = int(queue.name.split('library-case')[1].split('-')[0])
    if case not in done:
        rows.extend(r['task'] for r in json.loads(queue.read_text())['tasks'] if r['task'] not in attempted)
prefixes = ['primary','independent','helper','auxiliary','extra-a','extra-b','extra-c','extra-d','extra-e','extra-f','library-a','library-b','library-c','library-d','library-e','library-f']

def logdone(path):
    if not path.exists(): return False
    with path.open('rb') as source:
        source.seek(max(0, path.stat().st_size - 1200))
        return source.read().decode('utf8', errors='replace').rstrip().endswith('PASS: target declarations have clean transitive axiom audits.')

def candidates(prefilter):
    output = []; log_probes = 0; archive_probes = 0
    for task in rows:
        archive = transport_root / ('.t03-runtime-sync-' + Path(task).stem + '.zip')
        if prefilter:
            archive_probes += 1
            if not archive.exists(): continue
        passed = False
        for prefix in prefixes:
            log_probes += 1
            if logdone(E / (prefix + '-' + Path(task).stem + '.log')):
                passed = True; break
        if passed: continue
        if not prefilter:
            archive_probes += 1
            if not archive.exists(): continue
        output.append(task)
    return dict(tasks=output, log_probes=log_probes, archive_probes=archive_probes)

samples = []
for label, prefilter in [('prior', False), ('ready_archive_first', True), ('ready_archive_first_repeat', True)]:
    start = time.perf_counter(); result = candidates(prefilter)
    samples.append(dict(method=label, elapsed_seconds=time.perf_counter()-start, **result))
reference = set(samples[0]['tasks'])
assert all(set(sample['tasks']) == reference for sample in samples), 'Live candidate set changed; rerun with a fresh snapshot.'
record = E / a.output
assert not record.exists()
payload = dict(status='LIVE_QUEUE_ELIGIBILITY_EQUAL_NO_PROOF_PROCESSES_STARTED',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               unattempted_queue_rows=len(rows), samples=samples,
               compiler_processes_started=0, case_certificate_acceptances=0,
               scope='Source-readiness/log filtering only; all ordinary source/object validation remains required.')
record.write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps(payload), flush=True)
