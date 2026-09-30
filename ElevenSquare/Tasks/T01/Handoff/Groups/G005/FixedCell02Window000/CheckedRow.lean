import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window000.Cover
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window000.MedianCapture
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window000.Region001
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window000.Region002
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.FixedMedianRow
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SharedRosterBlockers

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window000
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def blockerPieces : List (QPoint × FeatureCapturePiece) := [
  (((1439673887/500000000), (497957757/500000000)), region001),
  (((1439673887/500000000), (359788647/500000000)), region002)]

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
  · have hh := hpartners (⟨3, by decide⟩, 8) (by simp [blockerIndices])
    exact SharedRosterBlockers.blocker_owned_for_partner P hc i (partner 3)
      hh.1 3 hh.2 _ (by
        change _ ∈ SharedFieldOwnership.sharedRosterCell03
        simp [SharedFieldOwnership.sharedRosterCell03])
  · have hh := hpartners (⟨3, by decide⟩, 9) (by simp [blockerIndices])
    exact SharedRosterBlockers.blocker_owned_for_partner P hc i (partner 3)
      hh.1 3 hh.2 _ (by
        change _ ∈ SharedFieldOwnership.sharedRosterCell03
        simp [SharedFieldOwnership.sharedRosterCell03])

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window000

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window000.capture_from_packing
