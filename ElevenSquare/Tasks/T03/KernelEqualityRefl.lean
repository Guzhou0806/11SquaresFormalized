import Lean.Elab.Tactic

/- Construct ordinary equality reflexivity from the right-hand expression.
   The declaration kernel still checks that the left-hand expression is equal.
   This avoids repeating an expensive coordinate reduction in the elaborator. -/
open Lean Meta Elab Tactic in
elab "t03_eq_refl" : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← goal.getType
  match type with
  | .app (.app (.app (.const ``Eq _) _) _) rhs =>
    goal.assign (← mkEqRefl rhs)
    replaceMainGoal []
  | _ => throwError "t03_eq_refl requires an equality goal"
