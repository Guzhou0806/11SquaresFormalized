import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012.RowCapture
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012.MedianLink
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.MedianBroad

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem capture_from_packing (P : Packing 11 coverCap)
    (i j : Owner) (hij : i ≠ j)
    (hcell : ClosedCell 8 (normalizeCenter (P.squares i).center))
    (hother : ClosedCell 12 (normalizeCenter (P.squares j).center))
    (hotherChart : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ (P.squares j).axis = chartAxis s)
    (t : ℝ) (ha : (P.squares i).axis = chartAxis t)
    (hlt : ((3005/4096:ℚ):ℝ) ≤ t) (htu : t ≤ ((3355/4096:ℚ):ℝ)) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  apply capture_with_median P i j hij hcell hother hotherChart t ha hlt htu
  intro polygon hmem hcontains
  have heq : polygon = target00 := by
    simpa [rowCertificate] using hmem
  subst polygon
  obtain ⟨hbLo, hbHi⟩ := interval_in_representative t hlt htu
  apply Field03SymbolicCell04Regime008.target00_majority_broad (P.squares i)
    t ha hbLo hbHi
  simpa only [target00_eq_representative] using hcontains

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime012.capture_from_packing
