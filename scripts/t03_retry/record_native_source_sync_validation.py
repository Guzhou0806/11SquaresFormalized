"""Bind the measured synchronization to the additional genuine receipt-copy check."""
from pathlib import Path
import datetime, hashlib, json
import argparse
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--record',type=Path,required=True)
ap.add_argument('--runtime',type=Path,required=True)
ap.add_argument('--main-receipts',type=Path,required=True)
ap.add_argument('--helper',type=Path,required=True)
a=ap.parse_args()
record=a.record
p = json.loads(record.read_text())
assert p['status'] == 'EXACT_SOURCE_SYNC_COMPARISON_AND_BYTE_BINDING_CONTROLS_PASSED'
assert p['measured_native_gain'] and p['different_archive_digest_rejected_before_mutations']
runtime = a.runtime.resolve()
receipt_check = json.loads((runtime / 'native-source-sync.json').read_text())
assert receipt_check['archive_sha256'] == p['archive_sha256']
assert receipt_check['proof_receipts_created'] == receipt_check['lean_processes_started'] == 0
assert receipt_check['genuine_receipts_copied'] > 0
main = a.main_receipts.resolve()
copied = list((runtime / 'project/verification/handoff-cache').glob('*.json'))
assert len(copied) == receipt_check['genuine_receipts_copied']
bindings = {}
for path in copied:
    raw = path.read_bytes()
    assert raw == (main / path.name).read_bytes(), ('Provisional receipt differs from actual main record', path.name)
    bindings[path.name] = hashlib.sha256(raw).hexdigest()
p.update(helper_source_sha256=hashlib.sha256(a.helper.read_bytes()).hexdigest(),
         genuine_receipt_fixture_check=receipt_check, copied_genuine_receipt_bindings=bindings,
         all_copied_receipts_byte_identical_to_actual_main_records=True,
         validation_completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         helper_binding_scope='Same tested synchronization algorithm; validation-directory guard additionally permits the actual genuine receipt-copy check.')
record.write_text(json.dumps(p, indent=2) + '\n')
print(json.dumps(dict(status=p['status'], helper_source_sha256=p['helper_source_sha256'],
                     actual_genuine_receipts_verified=len(bindings), proof_receipts_created=0)), flush=True)
