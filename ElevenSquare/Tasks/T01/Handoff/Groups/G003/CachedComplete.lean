import ElevenSquare.Tasks.T01.Handoff.Groups.G003.CachedCell04
import ElevenSquare.Tasks.T01.Handoff.Groups.G003.CachedCell08
import ElevenSquare.Tasks.T01.Handoff.Groups.G003.Transfer
import ElevenSquare.Tasks.T01.Handoff.Plan

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G003.Cached
open ElevenSquare.Pending
noncomputable section

/-- Both majority captures hold on the complete closed angle chart. -/
theorem support_capture : SupportCapture :=
  support_capture_of_hybrid_windows cell04_windows cell08_windows

/-- The 43 checked windows exclude all 764 masks in this group. -/
theorem excluded (k : Fin 2184) (hk : k.val ∈ groupCases (3 : Group))
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P (caseMask k)) : False :=
  exclusion_of_capture support_capture k hk P hc ho

/-- Adapt the proved geometric exclusion to the unchanged public trace contract. -/
theorem certificate (k : Fin 2184) (hk : k.val ∈ groupCases (3 : Group)) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  refine ⟨emptyState, emptyState, ?_, VerifiedTrace.refl _, Or.inl ⟨0, rfl⟩⟩
  intro P hc ho
  exact (excluded k hk P hc ho).elim

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G003.Cached

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G003.Cached.support_capture
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G003.Cached.excluded
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G003.Cached.certificate
