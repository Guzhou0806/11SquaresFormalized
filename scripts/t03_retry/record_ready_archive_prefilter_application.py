"""Bind the controller adoption and actual refill events; never accept proofs."""
from pathlib import Path
import argparse,datetime, hashlib, json

from retry_paths import kit_paths
ap=argparse.ArgumentParser();ap.add_argument('--kit',required=True);ap.add_argument('--transition',required=True);ap.add_argument('--benchmark',required=True);ap.add_argument('--controller-script',type=Path,required=True);ap.add_argument('--output',required=True)
a=ap.parse_args();K,E,_=kit_paths(a.kit)
assert all(Path(n).name==n and n.endswith('.json') for n in [a.transition,a.benchmark,a.output])
transition_path = E / a.transition
benchmark_path = E / a.benchmark
transition_raw = transition_path.read_bytes()
transition = json.loads(transition_raw)
benchmark_raw = benchmark_path.read_bytes()
benchmark = json.loads(benchmark_raw)
assert transition['compiler_processes_interrupted'] == 0
assert transition['maximum_parallel_checks'] == 6
assert benchmark['status'] == 'LIVE_QUEUE_ELIGIBILITY_EQUAL_NO_PROOF_PROCESSES_STARTED'
source = a.controller_script
assert hashlib.sha256(source.read_bytes()).hexdigest() == transition['controller_source_sha256']
pool = json.loads((E / 'unified-proof-pool-status.json').read_text())
cut = datetime.datetime.fromisoformat(transition['utc'])
pending = {}; samples = []
for event in pool['events']:
    when = datetime.datetime.fromisoformat(event['utc'])
    if when < cut: continue
    worker = event.get('worker')
    if event['status'] == 'CHECK_PASSED':
        pending[worker] = event
    elif event['status'] == 'CHECK_STARTED' and worker in pending:
        prior = pending.pop(worker)
        samples.append(dict(worker=worker, completed_task=prior['task'], next_task=event['task'],
                            completion_utc=prior['utc'], start_utc=event['utc'],
                            refill_delay_seconds=(when-datetime.datetime.fromisoformat(prior['utc'])).total_seconds(),
                            timestamp_order_valid=when >= datetime.datetime.fromisoformat(prior['utc'])))
assert len(samples) >= 2
record = E / a.output
assert not record.exists()
count = json.loads((E / 'RESULT.json').read_text())['completed_case_certificates']
payload = dict(status='SOURCE_READY_PREFILTER_APPLIED_EXISTING_PROOF_WORKERS_PRESERVED',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               transition=transition_path.name, transition_sha256=hashlib.sha256(transition_raw).hexdigest(),
               benchmark=benchmark_path.name, benchmark_sha256=hashlib.sha256(benchmark_raw).hexdigest(),
               controller_source_sha256=transition['controller_source_sha256'],
               completed_case_certificates=count, maximum_parallel_checks=6,
               controller_poll_seconds=5, compiler_processes_interrupted=0,
               actual_following_refill_events=samples,
               timing_scope='Observed controller events include scheduling and polling; they are not Lean compilation benchmarks.')
record.write_text(json.dumps(payload, indent=2) + '\n')
for row in samples:row['timestamp_order_valid']=row['refill_delay_seconds']>=0
payload['negative_or_reordered_refill_pairs']=[row for row in samples if row['refill_delay_seconds']<0]
payload['negative_pairs_excluded_from_interval_summaries']=True
record.write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps(dict(status=payload['status'], samples=len(samples),
                      first_refill_seconds=[r['refill_delay_seconds'] for r in samples[:2]], cases=count)))
