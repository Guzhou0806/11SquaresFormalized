#!/usr/bin/env python3
"""Validate a completed full replay; --write saves portable evidence and manifest.

Run after the final source/documentation edits and `verify.py --all` succeeds.
Stage intended new files first. This invokes no Lean and reuses no historical
pass claim: it checks current source/configuration/object hashes and every
receipt and axiom query. Historical provenance and focused audits stay intact.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True
from check_sources import ROOT, check, code_only, imports
from verify_support import audit_axioms, input_digest, priority_order

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
UNFINISHED = {'ElevenSquare.Pending.' + n for n in [
    'baseline_certificate_exists', 'prior_certificate_exists',
    'returned_certificate_exists', 'global_lower_bound']} | {
    'ElevenSquare.optimality', 'ElevenSquare.optimal_side_lower_bound'}
OUTPUTS = {'verification/wand125-upgrade.json', 'verification/source-check.json', 'MANIFEST.json'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(4 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def json_bytes(value):
    return (json.dumps(value, indent=2) + '\n').encode()


def collect_audit(root, source_check):
    """Verify the complete receipt graph before producing any portable output."""
    state = root / '.verification'
    result = json.loads((state / 'result.json').read_text())
    paths = (sorted((root / 'ElevenSquare').rglob('*.lean')) +
             sorted((root / 'Sqpack').rglob('*.lean')) +
             [root / 'ElevenSquare.lean', root / 'Sqpack.lean'])
    modules = {'.'.join(p.relative_to(root).with_suffix('').parts): p for p in paths}
    require(result.get('status') == 'PARTIAL_ASSEMBLY_COMPILES',
            'No successful full-project verifier result; run scripts/verify.py --all.')
    require(result.get('checked_modules') == len(modules),
            'The verifier result does not cover every current local module.')
    require(source_check.get('status') == 'SOURCE_ASSEMBLY_PASS'
            and source_check.get('local_modules') == len(modules)
            and source_check.get('explicit_admissions') == 6,
            'The source check must accept the full tree and exactly six inventoried admissions.')
    require(result.get('global_optimality_proved') is False,
            'Unexpected optimality status for this six-admission integration.')

    context = {p: sha(root / p) for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']}
    toolchain = (root / 'lean-toolchain').read_text().strip()
    version = toolchain.rsplit(':v', 1)[-1]
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    mathlib = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
    dependencies = {m: [d for d in imports(p) if d in modules] for m, p in modules.items()}
    order = priority_order(dependencies, {m: p.stat().st_size for m, p in modules.items()})
    source_hashes = {}; object_hashes = {}; input_ids = {}; axioms = {}
    compiler = None
    for m in order:
        receipt = json.loads((state / (m + '.json')).read_text())
        require(receipt.get('status') == 'accepted', 'Unaccepted module: ' + m)
        recorded = receipt.get('inputs', {})
        if compiler is None:
            compiler = recorded.get('compiler', '')
            parsed = re.search(r'\bversion ([^,]+),', compiler)
            require(parsed is not None and parsed[1] == version, 'Compiler/toolchain mismatch.')
        implicit = 'true' if m == 'Sqpack' or m.startswith('Sqpack.') else 'false'
        source = modules[m].read_bytes()
        source_hashes[m] = hashlib.sha256(source).hexdigest()
        current = {
            'source': source_hashes[m],
            'local_dependency_objects': {d: object_hashes[d] for d in dependencies[m]},
            'compiler': compiler,
            'arguments': ['-j1', '-M0', '-s65536', '-DautoImplicit=' + implicit, '-DmaxHeartbeats=0'],
            'build_context': context,
            'local_dependency_inputs': {d: input_ids[d] for d in dependencies[m]},
        }
        require(recorded == current, 'Stale source/configuration/dependency receipt: ' + m)
        target = root / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')
        object_hashes[m] = sha(target)
        require(receipt.get('object_sha256') == object_hashes[m], 'Changed compiled object: ' + m)
        input_ids[m] = input_digest(current)
        log = state / (m + '.log')
        require(log.is_file(), 'Missing compiler log: ' + m)
        if b'#print' in source:
            axioms.update(audit_axioms(code_only(source.decode()), log.read_text(), ALLOWED, UNFINISHED))
    require(UNFINISHED <= axioms.keys(), 'Missing final public target axiom queries.')
    require(axioms == result.get('axioms'), 'Verifier result does not match the current axiom logs.')
    require(any('sorryAx' in axioms[n] for n in UNFINISHED), 'Unexpected admission-free final audit.')
    return {
        'status': 'PARTIAL_ASSEMBLY_COMPILES',
        'scope': 'All local ElevenSquare and Sqpack modules; the six original admissions remain.',
        'checked_modules': len(modules), 'lean_toolchain': toolchain, 'mathlib_revision': mathlib,
        'full_upgrade_verified': True, 'global_optimality_proved': False,
        'explicit_native_admissions': 6, 'new_baseline_cases': 247,
        'build_context_sha256': context, 'source_sha256': dict(sorted(source_hashes.items())),
        'axioms': dict(sorted(axioms.items())),
    }


def publication(root, audit, source_check):
    """Prepare the full manifest in memory before modifying any evidence file."""
    def git_paths(*args):
        data = subprocess.check_output(['git', 'ls-files', *args, '-z'], cwd=root)
        return {p.decode() for p in data.split(b'\0') if p}
    tracked = git_paths('--cached')
    untracked = git_paths('--others', '--exclude-standard') - OUTPUTS
    require(not untracked, 'Stage intended new files before finalization: ' + ', '.join(sorted(untracked)))
    payloads = {'verification/wand125-upgrade.json': json_bytes(audit),
                'verification/source-check.json': json_bytes(source_check)}
    entries = []
    for rel in sorted((tracked | set(payloads)) - {'MANIFEST.json'}):
        path = root / rel
        require(rel in payloads or path.is_file(), 'Missing tracked file; stage its removal: ' + rel)
        if rel in payloads:
            data = payloads[rel]
            size, digest = len(data), hashlib.sha256(data).hexdigest()
        else:
            size, digest = path.stat().st_size, sha(path)
        entries.append({'path': rel, 'bytes': size, 'sha256': digest})
    payloads['MANIFEST.json'] = json_bytes({'format': 'sha256-source-manifest-v1', 'files': entries})
    return payloads


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='Save verified portable evidence and refresh MANIFEST.json.')
    args = parser.parse_args()
    # Missing/incomplete full results fail before the source scan.
    result_path = ROOT / '.verification/result.json'
    require(result_path.is_file(), 'No full-build result exists; complete scripts/verify.py --all first.')
    source_check = check(use_cache=True)
    audit = collect_audit(ROOT, source_check)
    if args.write:
        payloads = publication(ROOT, audit, source_check)
        for rel, data in payloads.items():
            path = ROOT / rel
            temporary = path.with_name(path.name + f'.{os.getpid()}.tmp')
            try:
                temporary.write_bytes(data)
                temporary.replace(path)
            finally:
                temporary.unlink(missing_ok=True)
        print('Saved ' + ', '.join(payloads) + '.')
    print(f"Validated {audit['checked_modules']} modules; six admissions remain; global optimality is unfinished.")
    if not args.write:
        print('No portable evidence changed. Use --write to publish the audit and source manifest.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, StopIteration, subprocess.CalledProcessError) as error:
        raise SystemExit('Finalization refused: ' + str(error)) from error
