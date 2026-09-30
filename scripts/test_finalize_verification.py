"""Finalization rejects incomplete/stale evidence, using tiny synthetic receipts."""
from pathlib import Path
import hashlib
import json
import tempfile
import unittest

from finalize_verification import UNFINISHED, collect_audit, json_bytes, sha
from verify_support import input_digest


class FinalizationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for name, text in {
            'lean-toolchain': 'leanprover/lean4:v4.34.1\n',
            'lakefile.lean': '-- synthetic fixture\n',
            'lake-manifest.json': json.dumps({'packages': [{'name': 'mathlib', 'rev': 'pin'}]}),
        }.items():
            (self.root / name).write_text(text)
        self.sources = {
            'ElevenSquare': '-- fixture\n',
            'Sqpack': '-- fixture\n',
            'ElevenSquare.Verification': 'import ElevenSquare\nimport Sqpack\n' +
                ''.join('#print axioms ' + n + '\n' for n in sorted(UNFINISHED)),
        }
        self.axioms = {n: ['sorryAx'] for n in sorted(UNFINISHED)}
        context = {p: sha(self.root / p) for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']}
        object_hashes = {}; inputs = {}
        state = self.root / '.verification'; state.mkdir()
        for module, text in self.sources.items():
            source = self.root / (module.replace('.', '/') + '.lean')
            source.parent.mkdir(parents=True, exist_ok=True); source.write_text(text)
            deps = ['ElevenSquare', 'Sqpack'] if module.endswith('.Verification') else []
            fingerprint = {
                'source': hashlib.sha256(text.encode()).hexdigest(),
                'local_dependency_objects': {d: object_hashes[d] for d in deps},
                'compiler': 'Lean (version 4.34.1, fixture)',
                'arguments': ['-j1', '-M0', '-s65536',
                              '-DautoImplicit=' + ('true' if module == 'Sqpack' else 'false'),
                              '-DmaxHeartbeats=0'],
                'build_context': context,
                'local_dependency_inputs': {d: input_digest(inputs[d]) for d in deps},
            }
            obj = self.root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
            obj.parent.mkdir(parents=True, exist_ok=True); obj.write_bytes(module.encode())
            object_hashes[module] = sha(obj); inputs[module] = fingerprint
            (state / (module + '.json')).write_bytes(json_bytes({
                'status': 'accepted', 'module': module, 'inputs': fingerprint,
                'object_sha256': object_hashes[module]}))
            output = ''.join("'" + n + "' depends on axioms: [sorryAx]\n" for n in sorted(UNFINISHED))
            (state / (module + '.log')).write_text(output if deps else '')
        self.result = {'status': 'PARTIAL_ASSEMBLY_COMPILES', 'checked_modules': 3,
                       'global_optimality_proved': False, 'axioms': self.axioms}
        self.save_result()
        self.source_check = {'status': 'SOURCE_ASSEMBLY_PASS', 'local_modules': 3, 'explicit_admissions': 6}

    def save_result(self):
        (self.root / '.verification/result.json').write_bytes(json_bytes(self.result))

    def test_complete_matching_receipts_are_accepted_without_writing(self):
        audit = collect_audit(self.root, self.source_check)
        self.assertTrue(audit['full_upgrade_verified'])
        self.assertEqual(audit['checked_modules'], 3)
        self.assertFalse((self.root / 'verification/wand125-upgrade.json').exists())

    def test_partial_result_is_rejected(self):
        self.result['checked_modules'] = 2; self.save_result()
        with self.assertRaisesRegex(ValueError, 'every current local module'):
            collect_audit(self.root, self.source_check)

    def test_changed_source_rejects_old_success(self):
        (self.root / 'ElevenSquare.lean').write_text('-- changed since success\n')
        with self.assertRaisesRegex(ValueError, 'Stale source'):
            collect_audit(self.root, self.source_check)

    def test_changed_dependency_configuration_rejects_old_success(self):
        (self.root / 'lakefile.lean').write_text('-- changed pin/configuration\n')
        with self.assertRaisesRegex(ValueError, 'Stale source/configuration'):
            collect_audit(self.root, self.source_check)

    def test_changed_object_rejects_old_success(self):
        (self.root / '.lake/build/lib/lean/ElevenSquare.olean').write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'Changed compiled object'):
            collect_audit(self.root, self.source_check)

    def test_changed_or_missing_axiom_evidence_rejects_old_success(self):
        self.result['axioms'] = {}; self.save_result()
        with self.assertRaisesRegex(ValueError, 'current axiom logs'):
            collect_audit(self.root, self.source_check)


if __name__ == '__main__':
    unittest.main()
