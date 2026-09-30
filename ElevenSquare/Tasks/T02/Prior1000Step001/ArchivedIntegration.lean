import ElevenSquare.Tasks.T02.Prior1000Step001.FirstStepLink
import ElevenSquare.Tasks.T02.Prior1000Step001.ArchivedOutput

namespace ElevenSquare.Tasks.T02.Prior1000Step001
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section

/-- The recorded rounded outer rows can be used by later ancestry, after the
stronger retained region has justified the ownership promotion. -/
theorem case1000_after_archived_second_step (P : Packing 11 coverCap)
    (hc : IsCharted P) (hocc : Occupies P (caseMask 1000)) :
    ∃ perm : Equiv.Perm Owner,
      StateHolds (relabelPacking P perm) (archivedNextState Prior1000FirstStep.nextState) := by
  obtain ⟨perm, hs⟩ := case1000_after_integer_second_step P hc hocc
  exact ⟨perm, archived_rows_holds _ _ hs⟩

end
end ElevenSquare.Tasks.T02.Prior1000Step001
