"""Replace a preserved external-reuse hold with the exact local proof barrier."""
from pathlib import Path
import argparse, datetime, hashlib, json
from retry_paths import kit_paths, low_priority_single_core
ap = argparse.ArgumentParser()
ap.add_argument('--case', type=int, required=True)
ap.add_argument('--kit',required=True)
ap.add_argument('--transport-dir')
ap.add_argument('--scratch-root',required=True)
ap.add_argument('--max-workers',type=int,default=1)
a=ap.parse_args();case=a.case
K,E,transport_root=kit_paths(a.kit,a.transport_dir)
scratch=Path(a.scratch_root).resolve();assert scratch.is_dir()
assert 1<=a.max_workers<=6
low_priority_single_core()

pub = json.loads((E / f'case{case}-packed-canonical-publication.json').read_text())
assert pub['case'] == case and pub['full_case_guard_retained_for_parallel_dependency_audits']
assert case not in {r['case'] for r in json.loads((E / 'RESULT.json').read_text())['audited_case_certificates']}
assert not any(j.get('case') == case for j in json.loads((E / 'unified-proof-pool-status.json').read_text())['active'].values())
guard = E / f'.collision-bool-preparing-case{case}.json'
old = guard.read_bytes()
assert json.loads(old)['status'] == 'NEW_CASE_TASK_HELD_FOR_EXTERNAL_CERTIFICATE_REUSE'
saved = E / f'case{case}-external-reuse-hold-before-local-resume.json'
assert not saved.exists()
saved.write_bytes(old)
assert saved.read_bytes() == old
p = dict(status='EXACT_GROUPED_RETRY_HELD_FOR_PARALLEL_DEPENDENCY_AUDITS', case=case,
         utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), required_dependency_groups=pub['groups'],
         exact_full_case_target=pub['original_target'], source_archive_sha256=pub['grouped_archive_sha256'],
         prior_hold=saved.name, prior_hold_sha256=hashlib.sha256(old).hexdigest(),
         reason='Continue the authorized local proof with the prepared exact source closure while external returned-case sources are unavailable.',
         maximum_global_compiler_checks=a.max_workers, maximum_live_chunk_archives=2,
         full_case_and_final_audits_pending=True)
guard.write_text(json.dumps(p, indent=2) + '\n')
(E / f'case{case}-local-check-resume.json').write_text(json.dumps(p, indent=2) + '\n')
print(json.dumps(p), flush=True)
