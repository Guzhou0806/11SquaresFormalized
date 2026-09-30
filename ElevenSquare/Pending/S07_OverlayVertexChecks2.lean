import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow16_correct : fractionRow16.map FractionPoint.rational = rationalRow16 := by
  simp only [fractionRow16, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check16 : integerHullCheck (integerOverlayPlanes ![1,2,7,4]) fractionRow16 = true := by decide
theorem vertices_fit16 (p : Point) (hp : p ∈ rationalHull rationalRow16) :
    ∀ g, ClosedCell ((![1,2,7,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow16_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check16 p hp
theorem fractionRow17_correct : fractionRow17.map FractionPoint.rational = rationalRow17 := by
  simp only [fractionRow17, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check17 : integerHullCheck (integerOverlayPlanes ![1,2,11,4]) fractionRow17 = true := by decide
theorem vertices_fit17 (p : Point) (hp : p ∈ rationalHull rationalRow17) :
    ∀ g, ClosedCell ((![1,2,11,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow17_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check17 p hp
theorem fractionRow18_correct : fractionRow18.map FractionPoint.rational = rationalRow18 := by
  simp only [fractionRow18, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check18 : integerHullCheck (integerOverlayPlanes ![1,3,7,0]) fractionRow18 = true := by decide
theorem vertices_fit18 (p : Point) (hp : p ∈ rationalHull rationalRow18) :
    ∀ g, ClosedCell ((![1,3,7,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow18_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check18 p hp
theorem fractionRow19_correct : fractionRow19.map FractionPoint.rational = rationalRow19 := by
  simp only [fractionRow19, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check19 : integerHullCheck (integerOverlayPlanes ![1,3,7,4]) fractionRow19 = true := by decide
theorem vertices_fit19 (p : Point) (hp : p ∈ rationalHull rationalRow19) :
    ∀ g, ClosedCell ((![1,3,7,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow19_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check19 p hp
theorem fractionRow20_correct : fractionRow20.map FractionPoint.rational = rationalRow20 := by
  simp only [fractionRow20, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check20 : integerHullCheck (integerOverlayPlanes ![2,0,11,8]) fractionRow20 = true := by decide
theorem vertices_fit20 (p : Point) (hp : p ∈ rationalHull rationalRow20) :
    ∀ g, ClosedCell ((![2,0,11,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow20_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check20 p hp
theorem fractionRow21_correct : fractionRow21.map FractionPoint.rational = rationalRow21 := by
  simp only [fractionRow21, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check21 : integerHullCheck (integerOverlayPlanes ![2,0,15,8]) fractionRow21 = true := by decide
theorem vertices_fit21 (p : Point) (hp : p ∈ rationalHull rationalRow21) :
    ∀ g, ClosedCell ((![2,0,15,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow21_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check21 p hp
theorem fractionRow22_correct : fractionRow22.map FractionPoint.rational = rationalRow22 := by
  simp only [fractionRow22, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check22 : integerHullCheck (integerOverlayPlanes ![2,1,11,4]) fractionRow22 = true := by decide
theorem vertices_fit22 (p : Point) (hp : p ∈ rationalHull rationalRow22) :
    ∀ g, ClosedCell ((![2,1,11,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow22_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check22 p hp
theorem fractionRow23_correct : fractionRow23.map FractionPoint.rational = rationalRow23 := by
  simp only [fractionRow23, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check23 : integerHullCheck (integerOverlayPlanes ![2,1,11,8]) fractionRow23 = true := by decide
theorem vertices_fit23 (p : Point) (hp : p ∈ rationalHull rationalRow23) :
    ∀ g, ClosedCell ((![2,1,11,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow23_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check23 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit16
