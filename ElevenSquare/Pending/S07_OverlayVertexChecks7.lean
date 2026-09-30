import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow56_correct : fractionRow56.map FractionPoint.rational = rationalRow56 := by
  simp only [fractionRow56, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check56 : integerHullCheck (integerOverlayPlanes ![5,2,6,5]) fractionRow56 = true := by decide
theorem vertices_fit56 (p : Point) (hp : p ∈ rationalHull rationalRow56) :
    ∀ g, ClosedCell ((![5,2,6,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow56_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check56 p hp
theorem fractionRow57_correct : fractionRow57.map FractionPoint.rational = rationalRow57 := by
  simp only [fractionRow57, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check57 : integerHullCheck (integerOverlayPlanes ![5,2,6,9]) fractionRow57 = true := by decide
theorem vertices_fit57 (p : Point) (hp : p ∈ rationalHull rationalRow57) :
    ∀ g, ClosedCell ((![5,2,6,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow57_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check57 p hp
theorem fractionRow58_correct : fractionRow58.map FractionPoint.rational = rationalRow58 := by
  simp only [fractionRow58, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check58 : integerHullCheck (integerOverlayPlanes ![5,2,7,0]) fractionRow58 = true := by decide
theorem vertices_fit58 (p : Point) (hp : p ∈ rationalHull rationalRow58) :
    ∀ g, ClosedCell ((![5,2,7,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow58_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check58 p hp
theorem fractionRow59_correct : fractionRow59.map FractionPoint.rational = rationalRow59 := by
  simp only [fractionRow59, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check59 : integerHullCheck (integerOverlayPlanes ![5,2,7,4]) fractionRow59 = true := by decide
theorem vertices_fit59 (p : Point) (hp : p ∈ rationalHull rationalRow59) :
    ∀ g, ClosedCell ((![5,2,7,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow59_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check59 p hp
theorem fractionRow60_correct : fractionRow60.map FractionPoint.rational = rationalRow60 := by
  simp only [fractionRow60, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check60 : integerHullCheck (integerOverlayPlanes ![5,2,7,5]) fractionRow60 = true := by decide
theorem vertices_fit60 (p : Point) (hp : p ∈ rationalHull rationalRow60) :
    ∀ g, ClosedCell ((![5,2,7,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow60_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check60 p hp
theorem fractionRow61_correct : fractionRow61.map FractionPoint.rational = rationalRow61 := by
  simp only [fractionRow61, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check61 : integerHullCheck (integerOverlayPlanes ![5,2,11,4]) fractionRow61 = true := by decide
theorem vertices_fit61 (p : Point) (hp : p ∈ rationalHull rationalRow61) :
    ∀ g, ClosedCell ((![5,2,11,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow61_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check61 p hp
theorem fractionRow62_correct : fractionRow62.map FractionPoint.rational = rationalRow62 := by
  simp only [fractionRow62, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check62 : integerHullCheck (integerOverlayPlanes ![5,3,7,0]) fractionRow62 = true := by decide
theorem vertices_fit62 (p : Point) (hp : p ∈ rationalHull rationalRow62) :
    ∀ g, ClosedCell ((![5,3,7,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow62_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check62 p hp
theorem fractionRow63_correct : fractionRow63.map FractionPoint.rational = rationalRow63 := by
  simp only [fractionRow63, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check63 : integerHullCheck (integerOverlayPlanes ![5,3,7,5]) fractionRow63 = true := by decide
theorem vertices_fit63 (p : Point) (hp : p ∈ rationalHull rationalRow63) :
    ∀ g, ClosedCell ((![5,3,7,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow63_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check63 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit56
