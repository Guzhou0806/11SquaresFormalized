import ElevenSquare.Tasks.T01.Field03Cell04Prefix009
import ElevenSquare.Tasks.T01.Field03Cell04Row009.PackingCapture

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- First ten adjacent closed intervals only, from zero through 5/128. -/
theorem field03_cell04_capture_first_ten (P : Packing 11 coverCap) (i j : Owner)
    (hij : i ≠ j)
    (hcell : ClosedCell 4 (normalizeCenter (P.squares i).center))
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (P.squares j).axis = chartAxis t)
    (t : ℝ) (ht0 : 0 ≤ t) (htop : t ≤ (5/128 : ℝ))
    (ha : (P.squares i).axis = chartAxis t) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  by_cases h9 : t ≤ (9/256 : ℝ)
  · exact field03_cell04_capture_first_nine P i j hij hcell hother hchart t ht0 h9 ha
  · have ht1 : t ≤ 1 := by linarith
    exact Field03Cell04Row009.capture_from_packing P i j hij hcell hother hchart
      t ht0 ht1 ha (le_of_lt (lt_of_not_ge h9)) htop

end
end ElevenSquare.Tasks.T01
