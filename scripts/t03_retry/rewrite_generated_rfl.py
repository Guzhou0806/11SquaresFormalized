"""Rewrite exact generated rfl tactic occurrences; every proof remains pending."""
import argparse, hashlib, json, re
from pathlib import Path
PATTERN=re.compile(rb'(?<=by )rfl\b|(?<=<;> )rfl\b')
HELPER=b'import ElevenSquare.Tasks.T03.KernelEqualityRefl\n'

def rewrite_generated_rfl(raw):
    changed,count=PATTERN.subn(b't03_eq_refl',raw)
    if not count: raise ValueError('No matching generated tactic occurrence; do not rewrite twice.')
    if HELPER not in changed: changed=HELPER+changed
    if re.findall(rb'\b[0-9]+\b',raw)!=re.findall(rb'\b[0-9]+\b',changed):
        raise ValueError('Numeric tokens changed.')
    return changed,count

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,required=True)
    p.add_argument('--source-sha256',required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();raw=a.source.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=a.source_sha256: raise SystemExit('Input source hash mismatch.')
    changed,count=rewrite_generated_rfl(raw)
    with a.output.open('xb') as f:f.write(changed)
    print(json.dumps({'status':'SOURCE_PREPARED_ALL_NEW_PROOFS_PENDING','proof_constructions_changed':count,
      'original_sha256':a.source_sha256,'new_sha256':hashlib.sha256(changed).hexdigest(),
      'numeric_tokens_unchanged':True,'compiler_started':False}))
if __name__=='__main__':main()
