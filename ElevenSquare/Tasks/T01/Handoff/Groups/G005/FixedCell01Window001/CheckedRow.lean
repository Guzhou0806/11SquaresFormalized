import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window001.Cover
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window001.MedianCapture
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedRow

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window001
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def certificate : FixedFeatureRow.Certificate 2 where
  targets := [.majority ⟨0, by decide⟩ medianTarget0, .majority ⟨1, by decide⟩ medianTarget1]
  cover := node000

theorem certificate_checked : certificate.Check G005.fixedFeatures G005.fixedThresholds inputRow := by
  refine ⟨?_, ?_⟩
  · exact cover_checked
  · intro target ht
    simp only [certificate, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact median_target0_majority
    · exact median_target1_majority

theorem capture_from_packing (P : Packing 11 coverCap) (hc : IsCharted P)
    (i : Owner) (partner : Fin 16 → Owner)
    (hrow : inputRow.contains (P.squares i))
    (hpartners : ∀ item ∈ blockerIndices,
      i ≠ partner item.1 ∧ ClosedCell item.1
        (normalizeCenter (P.squares (partner item.1)).center)) :
    G005.CaptureChoice (P.squares i) := by
  have howned : ∀ p ∈ certificate.blockerPoints,
      ∃ other : Owner, i ≠ other ∧ OpenSquare (P.squares other) (realPoint p) := by
    intro p hp
    change p ∈ ([] : List QPoint) at hp
    simp at hp
  obtain ⟨f, hf⟩ := FixedFeatureRow.packing_row_choice certificate
    G005.fixedFeatures G005.fixedThresholds inputRow certificate_checked P i hrow howned
  exact G005.captureChoice_of_fixedFeature (P.squares i) f hf

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window001

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window001.capture_from_packing
