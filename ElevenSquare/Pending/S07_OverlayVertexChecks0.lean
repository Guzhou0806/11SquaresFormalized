import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow0_correct : fractionRow0.map FractionPoint.rational = rationalRow0 := by
  simp only [fractionRow0, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check0 : integerHullCheck (integerOverlayPlanes ![0,2,7,0]) fractionRow0 = true := by decide
theorem vertices_fit0 (p : Point) (hp : p ∈ rationalHull rationalRow0) :
    ∀ g, ClosedCell ((![0,2,7,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow0_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check0 p hp
theorem fractionRow1_correct : fractionRow1.map FractionPoint.rational = rationalRow1 := by
  simp only [fractionRow1, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check1 : integerHullCheck (integerOverlayPlanes ![0,2,7,4]) fractionRow1 = true := by decide
theorem vertices_fit1 (p : Point) (hp : p ∈ rationalHull rationalRow1) :
    ∀ g, ClosedCell ((![0,2,7,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow1_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check1 p hp
theorem fractionRow2_correct : fractionRow2.map FractionPoint.rational = rationalRow2 := by
  simp only [fractionRow2, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check2 : integerHullCheck (integerOverlayPlanes ![0,3,3,0]) fractionRow2 = true := by decide
theorem vertices_fit2 (p : Point) (hp : p ∈ rationalHull rationalRow2) :
    ∀ g, ClosedCell ((![0,3,3,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow2_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check2 p hp
theorem fractionRow3_correct : fractionRow3.map FractionPoint.rational = rationalRow3 := by
  simp only [fractionRow3, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check3 : integerHullCheck (integerOverlayPlanes ![0,3,7,0]) fractionRow3 = true := by decide
theorem vertices_fit3 (p : Point) (hp : p ∈ rationalHull rationalRow3) :
    ∀ g, ClosedCell ((![0,3,7,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow3_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check3 p hp
theorem fractionRow4_correct : fractionRow4.map FractionPoint.rational = rationalRow4 := by
  simp only [fractionRow4, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check4 : integerHullCheck (integerOverlayPlanes ![0,7,2,0]) fractionRow4 = true := by decide
theorem vertices_fit4 (p : Point) (hp : p ∈ rationalHull rationalRow4) :
    ∀ g, ClosedCell ((![0,7,2,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow4_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check4 p hp
theorem fractionRow5_correct : fractionRow5.map FractionPoint.rational = rationalRow5 := by
  simp only [fractionRow5, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check5 : integerHullCheck (integerOverlayPlanes ![0,7,2,1]) fractionRow5 = true := by decide
theorem vertices_fit5 (p : Point) (hp : p ∈ rationalHull rationalRow5) :
    ∀ g, ClosedCell ((![0,7,2,1] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow5_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check5 p hp
theorem fractionRow6_correct : fractionRow6.map FractionPoint.rational = rationalRow6 := by
  simp only [fractionRow6, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check6 : integerHullCheck (integerOverlayPlanes ![0,7,2,5]) fractionRow6 = true := by decide
theorem vertices_fit6 (p : Point) (hp : p ∈ rationalHull rationalRow6) :
    ∀ g, ClosedCell ((![0,7,2,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow6_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check6 p hp
theorem fractionRow7_correct : fractionRow7.map FractionPoint.rational = rationalRow7 := by
  simp only [fractionRow7, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check7 : integerHullCheck (integerOverlayPlanes ![0,7,3,0]) fractionRow7 = true := by decide
theorem vertices_fit7 (p : Point) (hp : p ∈ rationalHull rationalRow7) :
    ∀ g, ClosedCell ((![0,7,3,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow7_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check7 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit0
