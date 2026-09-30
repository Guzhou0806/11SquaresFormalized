import ElevenSquare.Tasks.T01.Field03Cell04Prefix
import ElevenSquare.Tasks.T01.Field03Cell04Row003.PackingCapture
import ElevenSquare.Tasks.T01.Field03Cell04Row004.PackingCapture
import ElevenSquare.Tasks.T01.Field03Cell04Row005.PackingCapture
import ElevenSquare.Tasks.T01.Field03Cell04Row006.PackingCapture
import ElevenSquare.Tasks.T01.Field03Cell04Row007.PackingCapture
import ElevenSquare.Tasks.T01.Field03Cell04Row008.PackingCapture

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- First nine adjacent closed intervals only; no full-field or case exclusion. -/
theorem field03_cell04_capture_first_nine (P : Packing 11 coverCap) (i j : Owner)
    (hij : i ≠ j)
    (hcell : ClosedCell 4 (normalizeCenter (P.squares i).center))
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (P.squares j).axis = chartAxis t)
    (t : ℝ) (ht0 : 0 ≤ t) (htop : t ≤ (9/256 : ℝ))
    (ha : (P.squares i).axis = chartAxis t) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  have ht1 : t ≤ 1 := by linarith
  by_cases h2 : t ≤ (3/256 : ℝ)
  · exact field03_cell04_capture_first_three P i j hij hcell hother hchart t ht0 h2 ha
  by_cases h3 : t ≤ (1/64 : ℝ)
  · exact Field03Cell04Row003.capture_from_packing P i j hij hcell hother hchart t ht0 ht1 ha (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : t ≤ (5/256 : ℝ)
  · exact Field03Cell04Row004.capture_from_packing P i j hij hcell hother hchart t ht0 ht1 ha (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : t ≤ (3/128 : ℝ)
  · exact Field03Cell04Row005.capture_from_packing P i j hij hcell hother hchart t ht0 ht1 ha (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : t ≤ (7/256 : ℝ)
  · exact Field03Cell04Row006.capture_from_packing P i j hij hcell hother hchart t ht0 ht1 ha (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : t ≤ (1/32 : ℝ)
  · exact Field03Cell04Row007.capture_from_packing P i j hij hcell hother hchart t ht0 ht1 ha (le_of_lt (lt_of_not_ge h6)) h7
  exact Field03Cell04Row008.capture_from_packing P i j hij hcell hother hchart t ht0 ht1 ha (le_of_lt (lt_of_not_ge h7)) htop

end
end ElevenSquare.Tasks.T01
