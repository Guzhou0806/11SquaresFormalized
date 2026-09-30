import ElevenSquare.Tasks.T01.Field03Cell04Row000.PackingCapture
import ElevenSquare.Tasks.T01.Field03Cell04Row001.PackingCapture
import ElevenSquare.Tasks.T01.Field03Cell04Row002.PackingCapture

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- First three adjacent closed intervals. This covers only [0,3/256],
not the complete chart and not an indexed mask exclusion. -/
theorem field03_cell04_capture_first_three (P : Packing 11 coverCap) (i j : Owner)
    (hij : i ≠ j)
    (hcell : ClosedCell 4 (normalizeCenter (P.squares i).center))
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (P.squares j).axis = chartAxis t)
    (t : ℝ) (ht0 : 0 ≤ t) (htop : t ≤ (3/256 : ℝ))
    (ha : (P.squares i).axis = chartAxis t) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  have ht1 : t ≤ 1 := by linarith
  by_cases h0 : t ≤ (1/256 : ℝ)
  · exact Field03Cell04Row000.capture_from_packing P i j hij hcell hother hchart
      t ht0 ht1 ha ht0 h0
  by_cases h1 : t ≤ (1/128 : ℝ)
  · exact Field03Cell04Row001.capture_from_packing P i j hij hcell hother hchart
      t ht0 ht1 ha (le_of_lt (lt_of_not_ge h0)) h1
  · exact Field03Cell04Row002.capture_from_packing P i j hij hcell hother hchart
      t ht0 ht1 ha (le_of_lt (lt_of_not_ge h1)) htop

end
end ElevenSquare.Tasks.T01
