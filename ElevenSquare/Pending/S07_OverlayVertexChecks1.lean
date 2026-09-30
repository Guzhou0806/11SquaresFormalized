import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow8_correct : fractionRow8.map FractionPoint.rational = rationalRow8 := by
  simp only [fractionRow8, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check8 : integerHullCheck (integerOverlayPlanes ![0,7,3,1]) fractionRow8 = true := by decide
theorem vertices_fit8 (p : Point) (hp : p ∈ rationalHull rationalRow8) :
    ∀ g, ClosedCell ((![0,7,3,1] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow8_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check8 p hp
theorem fractionRow9_correct : fractionRow9.map FractionPoint.rational = rationalRow9 := by
  simp only [fractionRow9, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check9 : integerHullCheck (integerOverlayPlanes ![0,7,3,5]) fractionRow9 = true := by decide
theorem vertices_fit9 (p : Point) (hp : p ∈ rationalHull rationalRow9) :
    ∀ g, ClosedCell ((![0,7,3,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow9_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check9 p hp
theorem fractionRow10_correct : fractionRow10.map FractionPoint.rational = rationalRow10 := by
  simp only [fractionRow10, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check10 : integerHullCheck (integerOverlayPlanes ![0,7,7,0]) fractionRow10 = true := by decide
theorem vertices_fit10 (p : Point) (hp : p ∈ rationalHull rationalRow10) :
    ∀ g, ClosedCell ((![0,7,7,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow10_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check10 p hp
theorem fractionRow11_correct : fractionRow11.map FractionPoint.rational = rationalRow11 := by
  simp only [fractionRow11, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check11 : integerHullCheck (integerOverlayPlanes ![0,7,7,5]) fractionRow11 = true := by decide
theorem vertices_fit11 (p : Point) (hp : p ∈ rationalHull rationalRow11) :
    ∀ g, ClosedCell ((![0,7,7,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow11_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check11 p hp
theorem fractionRow12_correct : fractionRow12.map FractionPoint.rational = rationalRow12 := by
  simp only [fractionRow12, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check12 : integerHullCheck (integerOverlayPlanes ![1,1,7,4]) fractionRow12 = true := by decide
theorem vertices_fit12 (p : Point) (hp : p ∈ rationalHull rationalRow12) :
    ∀ g, ClosedCell ((![1,1,7,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow12_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check12 p hp
theorem fractionRow13_correct : fractionRow13.map FractionPoint.rational = rationalRow13 := by
  simp only [fractionRow13, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check13 : integerHullCheck (integerOverlayPlanes ![1,1,11,4]) fractionRow13 = true := by decide
theorem vertices_fit13 (p : Point) (hp : p ∈ rationalHull rationalRow13) :
    ∀ g, ClosedCell ((![1,1,11,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow13_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check13 p hp
theorem fractionRow14_correct : fractionRow14.map FractionPoint.rational = rationalRow14 := by
  simp only [fractionRow14, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check14 : integerHullCheck (integerOverlayPlanes ![1,1,11,8]) fractionRow14 = true := by decide
theorem vertices_fit14 (p : Point) (hp : p ∈ rationalHull rationalRow14) :
    ∀ g, ClosedCell ((![1,1,11,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow14_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check14 p hp
theorem fractionRow15_correct : fractionRow15.map FractionPoint.rational = rationalRow15 := by
  simp only [fractionRow15, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check15 : integerHullCheck (integerOverlayPlanes ![1,2,7,0]) fractionRow15 = true := by decide
theorem vertices_fit15 (p : Point) (hp : p ∈ rationalHull rationalRow15) :
    ∀ g, ClosedCell ((![1,2,7,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow15_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check15 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit8
