import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow72_correct : fractionRow72.map FractionPoint.rational = rationalRow72 := by
  simp only [fractionRow72, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check72 : integerHullCheck (integerOverlayPlanes ![5,7,3,5]) fractionRow72 = true := by decide
theorem vertices_fit72 (p : Point) (hp : p ∈ rationalHull rationalRow72) :
    ∀ g, ClosedCell ((![5,7,3,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow72_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check72 p hp
theorem fractionRow73_correct : fractionRow73.map FractionPoint.rational = rationalRow73 := by
  simp only [fractionRow73, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check73 : integerHullCheck (integerOverlayPlanes ![5,7,7,0]) fractionRow73 = true := by decide
theorem vertices_fit73 (p : Point) (hp : p ∈ rationalHull rationalRow73) :
    ∀ g, ClosedCell ((![5,7,7,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow73_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check73 p hp
theorem fractionRow74_correct : fractionRow74.map FractionPoint.rational = rationalRow74 := by
  simp only [fractionRow74, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check74 : integerHullCheck (integerOverlayPlanes ![5,7,7,5]) fractionRow74 = true := by decide
theorem vertices_fit74 (p : Point) (hp : p ∈ rationalHull rationalRow74) :
    ∀ g, ClosedCell ((![5,7,7,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow74_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check74 p hp
theorem fractionRow75_correct : fractionRow75.map FractionPoint.rational = rationalRow75 := by
  simp only [fractionRow75, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check75 : integerHullCheck (integerOverlayPlanes ![6,4,10,10]) fractionRow75 = true := by decide
theorem vertices_fit75 (p : Point) (hp : p ∈ rationalHull rationalRow75) :
    ∀ g, ClosedCell ((![6,4,10,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow75_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check75 p hp
theorem fractionRow76_correct : fractionRow76.map FractionPoint.rational = rationalRow76 := by
  simp only [fractionRow76, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check76 : integerHullCheck (integerOverlayPlanes ![6,4,10,13]) fractionRow76 = true := by decide
theorem vertices_fit76 (p : Point) (hp : p ∈ rationalHull rationalRow76) :
    ∀ g, ClosedCell ((![6,4,10,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow76_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check76 p hp
theorem fractionRow77_correct : fractionRow77.map FractionPoint.rational = rationalRow77 := by
  simp only [fractionRow77, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check77 : integerHullCheck (integerOverlayPlanes ![6,5,6,9]) fractionRow77 = true := by decide
theorem vertices_fit77 (p : Point) (hp : p ∈ rationalHull rationalRow77) :
    ∀ g, ClosedCell ((![6,5,6,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow77_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check77 p hp
theorem fractionRow78_correct : fractionRow78.map FractionPoint.rational = rationalRow78 := by
  simp only [fractionRow78, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check78 : integerHullCheck (integerOverlayPlanes ![6,5,10,9]) fractionRow78 = true := by decide
theorem vertices_fit78 (p : Point) (hp : p ∈ rationalHull rationalRow78) :
    ∀ g, ClosedCell ((![6,5,10,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow78_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check78 p hp
theorem fractionRow79_correct : fractionRow79.map FractionPoint.rational = rationalRow79 := by
  simp only [fractionRow79, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check79 : integerHullCheck (integerOverlayPlanes ![6,5,10,13]) fractionRow79 = true := by decide
theorem vertices_fit79 (p : Point) (hp : p ∈ rationalHull rationalRow79) :
    ∀ g, ClosedCell ((![6,5,10,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow79_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check79 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit72
