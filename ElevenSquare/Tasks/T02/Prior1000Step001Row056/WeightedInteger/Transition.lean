import ElevenSquare.Tasks.T02.Prior1000Step001Row056.WeightedInteger.Sound
import ElevenSquare.Tasks.T02.Prior1000Step001Row056.TransitionChecks
import ElevenSquare.Tasks.T02.IntegerRowTransitions

namespace ElevenSquare.Tasks.T02.Prior1000Step001Row056.WeightedInteger
open ElevenSquare.Pending ElevenSquare.Tasks.T02
open IntegerCover
noncomputable section

theorem transition_checked_of_owned (s : PoseState) (ho : s.owned = ownedByRole) :
    IntegerTransitionCheck s (6 : Owner) predecessorRow transition integerCertificate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [transition, ho] using transition_self_cuts_checked
  · simpa only [transition, ho] using transition_domain_implied
  · exact coverage_checked
  · simpa only [transition, RowTransitionCertificate.inputRow,
      ForbiddenPiece.Check, checkState, ho] using forbidden_checked

theorem seed_row_retained {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (hs : StateHolds P s) (ho : s.owned = ownedByRole)
    (hq : predecessorRow.contains (P.squares (6 : Owner))) :
    retainedRow.contains (P.squares (6 : Owner)) := by
  have hout := integer_row_transition_keeps P s hs (6 : Owner) predecessorRow transition
    integerCertificate (transition_checked_of_owned s ho) hq
  rw [transition_output_matches] at hout
  obtain ⟨r, hr, hcontains⟩ := hout
  simpa only [List.mem_singleton.mp hr] using hcontains

end
end ElevenSquare.Tasks.T02.Prior1000Step001Row056.WeightedInteger
