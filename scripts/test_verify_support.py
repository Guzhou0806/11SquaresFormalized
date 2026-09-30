"""Small verifier regressions; uses no Lean process or real build cache."""
import unittest

from verify_support import audit_axioms, input_digest, priority_order, reusable_inputs


class VerificationSupportTests(unittest.TestCase):
    def test_shared_interfaces_first_and_audit_last(self):
        deps = {'Data': [], 'Shared': [], 'A': ['Shared'], 'B': ['Shared'],
                'Leaf': ['Data'], 'ElevenSquare.Verification': ['A', 'Leaf']}
        order = priority_order(deps, {m: 1 for m in deps})
        self.assertEqual(order[0], 'Shared')
        self.assertEqual(order[-1], 'ElevenSquare.Verification')
        for m, ds in deps.items():
            for dep in ds:
                self.assertLess(order.index(dep), order.index(m))

    def test_cycle_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'cycle'):
            priority_order({'A': ['B'], 'B': ['A']}, {'A': 1, 'B': 1})

    def test_legacy_receipt_reused_only_with_original_inputs_and_times(self):
        old = {'source': 'same', 'local_dependency_objects': {'A': 'object'}}
        current = dict(old, build_context={'manifest': 'pinned'},
                       local_dependency_inputs={'A': 'inputs'})
        self.assertTrue(reusable_inputs(old, current, legacy_baseline=True,
                                        checked_at=20, newest_input=10))
        self.assertFalse(reusable_inputs(old, current, legacy_baseline=True,
                                         checked_at=20, newest_input=21))
        self.assertFalse(reusable_inputs(old, current, legacy_baseline=False,
                                         checked_at=20, newest_input=10))

    def test_transitive_change_invalidates_even_with_same_dependency_object(self):
        before_a = {'source': 'before'}
        after_a = {'source': 'after'}
        before_b = {'source': 'same B', 'dependency': input_digest(before_a)}
        after_b = {'source': 'same B', 'dependency': input_digest(after_a)}
        before_c = {'source': 'same C', 'local_dependency_objects': {'B': 'same object'},
                    'local_dependency_inputs': {'B': input_digest(before_b)}, 'build_context': {}}
        after_c = dict(before_c, local_dependency_inputs={'B': input_digest(after_b)})
        self.assertFalse(reusable_inputs(before_c, after_c, legacy_baseline=True,
                                         checked_at=20, newest_input=10))
        self.assertTrue(reusable_inputs(after_c, after_c, legacy_baseline=False,
                                        checked_at=20, newest_input=30))

    def test_short_and_private_names_resolve_by_output_order(self):
        source = '#print axioms local_result\n#print axioms local_result\n'
        output = ("'A.local_result' depends on axioms: [propext]\n"
                  "'_private.X.0.B.local_result' does not depend on any axioms\n")
        self.assertEqual(audit_axioms(source, output, {'propext'}, set()),
                         {'A.local_result': ['propext'], '_private.X.0.B.local_result': []})

    def test_missing_output_and_unapproved_axiom_fail(self):
        with self.assertRaisesRegex(ValueError, 'Expected'):
            audit_axioms('#print axioms A.x', '', set(), set())
        with self.assertRaisesRegex(ValueError, 'Unapproved'):
            audit_axioms('#print axioms x', "'A.x' depends on axioms: [sorryAx]",
                         set(), {'Other.x'})
        self.assertEqual(audit_axioms('#print axioms x',
                         "'A.x' depends on axioms: [sorryAx]", set(), {'A.x'}),
                         {'A.x': ['sorryAx']})


if __name__ == '__main__':
    unittest.main()
