import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window017.Cover
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window017.MedianCapture
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window017.Region001
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window017.Region002
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.FixedMedianRow
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SharedRosterBlockers

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window017
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def blockerPieces : List (QPoint × FeatureCapturePiece) := [
  (((598058557561106414706741913/200000000000000000000000000), (19894392534717634717104431/25000000000000000000000000)), region001),
  (((180050283/62500000), (1448584901/1000000000)), region002)]

theorem blocker_pieces_checked : ∀ b ∈ blockerPieces, b.2.Check [b.1] inputRow := by
  intro b hb
  simp only [blockerPieces, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simpa only [region001Feature] using region001_checked
  · simpa only [region002Feature] using region002_checked

theorem capture_from_packing (P : Packing 11 coverCap) (hc : IsCharted P)
    (i : Owner) (partner : Fin 16 → Owner)
    (hrow : inputRow.contains (P.squares i))
    (hpartners : ∀ item ∈ blockerIndices,
      i ≠ partner item.1 ∧ ClosedCell item.1
        (normalizeCenter (P.squares (partner item.1)).center)) :
    BaselineMajorityCapture G005.featureA 3 (P.squares i) := by
  apply FixedMedianRow.packing_majority G005.featureA 3 inputRow
    medianTarget blockerPieces node000 cover_checked median_target_majority
    blocker_pieces_checked P i hrow
  intro b hb
  simp only [blockerPieces, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · have hh := hpartners (⟨3, by decide⟩, 0) (by simp [blockerIndices])
    exact SharedRosterBlockers.blocker_owned_for_partner P hc i (partner 3)
      hh.1 3 hh.2 _ (by
        change _ ∈ SharedFieldOwnership.sharedRosterCell03
        simp [SharedFieldOwnership.sharedRosterCell03])
  · have hh := hpartners (⟨7, by decide⟩, 11) (by simp [blockerIndices])
    exact SharedRosterBlockers.blocker_owned_for_partner P hc i (partner 7)
      hh.1 7 hh.2 _ (by
        change _ ∈ SharedFieldOwnership.sharedRosterCell07
        simp [SharedFieldOwnership.sharedRosterCell07])

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window017

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window017.capture_from_packing
