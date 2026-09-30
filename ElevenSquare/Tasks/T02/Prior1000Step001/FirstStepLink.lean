import ElevenSquare.Tasks.T02.Prior1000Step001.SeedLink
import ElevenSquare.Tasks.T02.Prior1000FirstStep.SharedCoreComplete

namespace ElevenSquare.Tasks.T02.Prior1000Step001
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section
set_option maxRecDepth 100000

/-- Step 0 updates owner 4; the exact owner-6 rows used by step 1 are unchanged. -/
theorem first_step_rows :
    Prior1000FirstStep.nextState.rows (6 : Owner) = predecessorRows := by
  rw [predecessor_rows_eq_seed]
  rfl

/-- Exact equality includes the updated owner-4 hull and every other owner. -/
theorem first_step_owned : Prior1000FirstStep.nextState.owned = ownedByRole := by
  funext i
  fin_cases i <;> rational_decide

def secondState : PoseState := nextState Prior1000FirstStep.nextState

theorem second_step_from_first {S : ℝ} (P : Packing 11 S)
    (hs : StateHolds P Prior1000FirstStep.nextState) :
    StateHolds P secondState :=
  step_holds P Prior1000FirstStep.nextState hs first_step_rows first_step_owned

/-- Two consecutive pruning-and-ownership steps from an actual initialized
packing, preserving closed angle endpoints and the same owner permutation. -/
theorem case1000_after_integer_second_step (P : Packing 11 coverCap)
    (hc : IsCharted P) (hocc : Occupies P (caseMask 1000)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) secondState := by
  obtain ⟨perm, hs⟩ := Prior1000FirstStep.SharedCore.case1000_after_integer_first_step P hc hocc
  exact ⟨perm, second_step_from_first _ hs⟩

end
end ElevenSquare.Tasks.T02.Prior1000Step001
