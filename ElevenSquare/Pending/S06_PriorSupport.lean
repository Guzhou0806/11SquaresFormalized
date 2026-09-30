import ElevenSquare.Tasks.T02.Exclusion
import ElevenSquare.Pending.S06_Baseline

/-! UNFINISHED FORMALIZATION OBLIGATIONS. See handoffs/S06_PriorSupport.md.
Every `sorry` in this file is an explicit outstanding proof, not verified evidence. -/

namespace ElevenSquare.Pending
noncomputable section

-- Dependency deliberately stops at the original 1931 exclusions.
-- Any early D4 support halfplanes used by these 76 certificates must be proved
-- from this premise, never from S07_Bridge or the final 2180-case conclusion.
theorem prior_certificate_exists
    (hbase : ∀ k : Fin 2184, k.val ∈ baselineIndices → Excluded k)
    (k : Fin 2184) (hk : k.val ∈ priorIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  sorry

theorem prior_excluded
    (hbase : ∀ k : Fin 2184, k.val ∈ baselineIndices → Excluded k)
    (k : Fin 2184) (hk : k.val ∈ priorIndices) : Excluded k := by
  obtain ⟨a, b, hroot, htrace, hterminal⟩ := prior_certificate_exists hbase k hk
  exact ElevenSquare.Tasks.T02.excludes_of_terminal_trace
    (caseMask k) a b hroot htrace hterminal


end
end ElevenSquare.Pending
