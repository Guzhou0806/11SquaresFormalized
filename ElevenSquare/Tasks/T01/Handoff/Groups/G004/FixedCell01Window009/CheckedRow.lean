import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window009.Cover
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window009.MedianCapture
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window009.Region001
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.FixedMedianRow
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SharedRosterBlockers

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window009
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def blockerPieces : List (QPoint × FeatureCapturePiece) := [
  (((498020679/500000000), (872404559/1000000000)), region001)]

theorem blocker_pieces_checked : ∀ b ∈ blockerPieces, b.2.Check [b.1] inputRow := by
  intro b hb
  simp only [blockerPieces, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · simpa only [region001Feature] using region001_checked

theorem capture_from_packing (P : Packing 11 coverCap) (hc : IsCharted P)
    (i : Owner) (partner : Fin 16 → Owner)
    (hrow : inputRow.contains (P.squares i))
    (hpartners : ∀ item ∈ blockerIndices,
      i ≠ partner item.1 ∧ ClosedCell item.1
        (normalizeCenter (P.squares (partner item.1)).center)) :
    BaselineMajorityCapture G004.featureSites 3 (P.squares i) := by
  apply FixedMedianRow.packing_majority G004.featureSites 3 inputRow
    medianTarget blockerPieces node000 cover_checked median_target_majority
    blocker_pieces_checked P i hrow
  intro b hb
  simp only [blockerPieces, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · have hh := hpartners (⟨0, by decide⟩, 5) (by simp [blockerIndices])
    exact SharedRosterBlockers.blocker_owned_for_partner P hc i (partner 0)
      hh.1 0 hh.2 _ (by
        change _ ∈ SharedFieldOwnership.sharedRosterCell00
        simp [SharedFieldOwnership.sharedRosterCell00])

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window009

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window009.capture_from_packing
