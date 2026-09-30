import ElevenSquare.Tasks.T03.Exclusion
import ElevenSquare.Pending.S06_Baseline

/-! UNFINISHED FORMALIZATION OBLIGATIONS. See handoffs/S06_Returned.md.
Every `sorry` in this file is an explicit outstanding proof, not verified evidence. -/

namespace ElevenSquare.Pending
noncomputable section

-- 173 actual returned indices, independent of the final D4 bridge.
theorem returned_certificate_exists (k : Fin 2184) (hk : k.val ∈ returnedIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  sorry

theorem returned_excluded (k : Fin 2184) (hk : k.val ∈ returnedIndices) : Excluded k := by
  obtain ⟨a, b, hroot, htrace, hterminal⟩ := returned_certificate_exists k hk
  exact ElevenSquare.Tasks.T03.excludes_of_terminal_trace
    (caseMask k) a b hroot htrace hterminal


end
end ElevenSquare.Pending
