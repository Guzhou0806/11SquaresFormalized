import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell05
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell09
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10
import ElevenSquare.Tasks.T01.Handoff.Plan

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending
noncomputable section

theorem support_capture : SupportCapture :=
  support_capture_of_fixed_windows fixedCell05_windows fixedCell09_windows fixedCell10_windows

theorem excluded (k : Fin 2184) (hk : k.val ∈ groupCases (7 : Group))
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P (caseMask k)) : False :=
  exclusion_of_capture support_capture k hk P hc ho

theorem certificate (k : Fin 2184) (hk : k.val ∈ groupCases (7 : Group)) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  refine ⟨emptyState, emptyState, ?_, VerifiedTrace.refl _, Or.inl ⟨0, rfl⟩⟩
  intro P hc ho
  exact (excluded k hk P hc ho).elim

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.support_capture
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.excluded
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.certificate
