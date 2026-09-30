import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow216_correct : fractionRow216.map FractionPoint.rational = rationalRow216 := by
  simp only [fractionRow216, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check216 : integerHullCheck (integerOverlayPlanes ![15,12,8,15]) fractionRow216 = true := by decide
theorem vertices_fit216 (p : Point) (hp : p ∈ rationalHull rationalRow216) :
    ∀ g, ClosedCell ((![15,12,8,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow216_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check216 p hp
theorem fractionRow217_correct : fractionRow217.map FractionPoint.rational = rationalRow217 := by
  simp only [fractionRow217, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check217 : integerHullCheck (integerOverlayPlanes ![15,12,12,15]) fractionRow217 = true := by decide
theorem vertices_fit217 (p : Point) (hp : p ∈ rationalHull rationalRow217) :
    ∀ g, ClosedCell ((![15,12,12,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow217_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check217 p hp
theorem fractionRow218_correct : fractionRow218.map FractionPoint.rational = rationalRow218 := by
  simp only [fractionRow218, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check218 : integerHullCheck (integerOverlayPlanes ![15,13,8,11]) fractionRow218 = true := by decide
theorem vertices_fit218 (p : Point) (hp : p ∈ rationalHull rationalRow218) :
    ∀ g, ClosedCell ((![15,13,8,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow218_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check218 p hp
theorem fractionRow219_correct : fractionRow219.map FractionPoint.rational = rationalRow219 := by
  simp only [fractionRow219, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check219 : integerHullCheck (integerOverlayPlanes ![15,13,8,15]) fractionRow219 = true := by decide
theorem vertices_fit219 (p : Point) (hp : p ∈ rationalHull rationalRow219) :
    ∀ g, ClosedCell ((![15,13,8,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow219_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check219 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit216
