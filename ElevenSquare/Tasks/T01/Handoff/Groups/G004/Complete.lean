import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell02
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.Transfer
import ElevenSquare.Tasks.T01.Handoff.Plan

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004
open ElevenSquare.Pending
noncomputable section

theorem support_capture : SupportCapture :=
  support_capture_of_fixed_windows fixedCell01_windows fixedCell02_windows

theorem excluded (k : Fin 2184) (hk : k.val ∈ groupCases (4 : Group))
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P (caseMask k)) : False :=
  exclusion_of_capture support_capture k hk P hc ho

theorem certificate (k : Fin 2184) (hk : k.val ∈ groupCases (4 : Group)) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  refine ⟨emptyState, emptyState, ?_, VerifiedTrace.refl _, Or.inl ⟨0, rfl⟩⟩
  intro P hc ho
  exact (excluded k hk P hc ho).elim

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.support_capture
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.excluded
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.certificate
