import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime001.Bridge
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime001.TargetCheck
import ElevenSquare.Tasks.T01.Field03Feature

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime001
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem row_certificate_checked : rowCertificate.Check 4 (161/4096) (309/2048) := by
  refine ⟨source_eq, ?_, row_targets_checked⟩
  change node000.Check source
    (rowCertificate.targets.map SymbolicFieldTarget.polygon) (161/4096) (309/2048)
  rw [row_targetPolygons_eq]
  exact cover_checked

theorem capture_with_median (P : Packing 11 coverCap)
    (i j : Owner) (hij : i ≠ j)
    (hcell : ClosedCell 4 (normalizeCenter (P.squares i).center))
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hotherChart : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ (P.squares j).axis = chartAxis s)
    (t : ℝ) (ha : (P.squares i).axis = chartAxis t)
    (hlt : ((161/4096:ℚ):ℝ) ≤ t) (htu : t ≤ ((309/2048:ℚ):ℝ))
    (hmedian : ∀ polygon,
      SymbolicFieldTarget.median polygon ∈ rowCertificate.targets →
      SymbolicPolygonContains polygon t (P.squares i).center →
      BaselineMajorityCapture baselineField03Sites 2 (P.squares i)) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  apply symbolic_field_row_majority P i 4 baselineField03Sites t
    (161/4096) (309/2048) rowCertificate row_certificate_checked
    hlt htu ha hcell hmedian
  intro p hp
  rw [row_blockerPoints_eq] at hp
  exact blockerPoints_owned P i j hij hother hotherChart p hp

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime001

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime001.capture_with_median
