import Mathlib.Data.Rat.Defs
import Lean.Elab.Tactic.ElabTerm

/-!
# Ordinary-kernel decision proofs for closed rational checks

Batteries marks the arithmetic operations on `Rat` irreducible to protect normal
simplification. The built-in `decide` tactic therefore stops at those operations.
`rational_decide` temporarily makes just these operations semireducible and calls
ordinary `decide`. Its result is the usual `of_decide_eq_true ... rfl` proof term,
which the kernel independently checks by reduction. The original reducibility
settings are restored afterward; no compiled evaluation or additional logical
axiom is involved.

For large finite checks, callers may need `set_option maxRecDepth 10000` and an
appropriate `maxHeartbeats` setting. This tactic requires a closed proposition
with a constructive `Decidable` instance, exactly as ordinary `decide` does.
-/

namespace ElevenSquare.Tasks.T02
open Lean Elab Tactic

/-- Ordinary `decide` with rational arithmetic exposed only during this tactic. -/
elab "rational_decide" : tactic => withoutModifyingEnv do
  for declaration in [``Rat.add, ``Rat.sub, ``Rat.mul, ``Rat.inv, ``Rat.ofScientific] do
    setReducibilityStatus declaration .semireducible
  evalTactic (← `(tactic| decide))

end ElevenSquare.Tasks.T02
