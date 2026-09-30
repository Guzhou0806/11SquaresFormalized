import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow32_correct : fractionRow32.map FractionPoint.rational = rationalRow32 := by
  simp only [fractionRow32, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check32 : integerHullCheck (integerOverlayPlanes ![2,5,11,9]) fractionRow32 = true := by decide
theorem vertices_fit32 (p : Point) (hp : p ∈ rationalHull rationalRow32) :
    ∀ g, ClosedCell ((![2,5,11,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow32_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check32 p hp
theorem fractionRow33_correct : fractionRow33.map FractionPoint.rational = rationalRow33 := by
  simp only [fractionRow33, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check33 : integerHullCheck (integerOverlayPlanes ![2,5,15,8]) fractionRow33 = true := by decide
theorem vertices_fit33 (p : Point) (hp : p ∈ rationalHull rationalRow33) :
    ∀ g, ClosedCell ((![2,5,15,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow33_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check33 p hp
theorem fractionRow34_correct : fractionRow34.map FractionPoint.rational = rationalRow34 := by
  simp only [fractionRow34, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check34 : integerHullCheck (integerOverlayPlanes ![3,0,15,8]) fractionRow34 = true := by decide
theorem vertices_fit34 (p : Point) (hp : p ∈ rationalHull rationalRow34) :
    ∀ g, ClosedCell ((![3,0,15,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow34_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check34 p hp
theorem fractionRow35_correct : fractionRow35.map FractionPoint.rational = rationalRow35 := by
  simp only [fractionRow35, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check35 : integerHullCheck (integerOverlayPlanes ![3,0,15,12]) fractionRow35 = true := by decide
theorem vertices_fit35 (p : Point) (hp : p ∈ rationalHull rationalRow35) :
    ∀ g, ClosedCell ((![3,0,15,12] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow35_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check35 p hp
theorem fractionRow36_correct : fractionRow36.map FractionPoint.rational = rationalRow36 := by
  simp only [fractionRow36, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check36 : integerHullCheck (integerOverlayPlanes ![3,1,11,8]) fractionRow36 = true := by decide
theorem vertices_fit36 (p : Point) (hp : p ∈ rationalHull rationalRow36) :
    ∀ g, ClosedCell ((![3,1,11,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow36_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check36 p hp
theorem fractionRow37_correct : fractionRow37.map FractionPoint.rational = rationalRow37 := by
  simp only [fractionRow37, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check37 : integerHullCheck (integerOverlayPlanes ![3,1,15,8]) fractionRow37 = true := by decide
theorem vertices_fit37 (p : Point) (hp : p ∈ rationalHull rationalRow37) :
    ∀ g, ClosedCell ((![3,1,15,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow37_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check37 p hp
theorem fractionRow38_correct : fractionRow38.map FractionPoint.rational = rationalRow38 := by
  simp only [fractionRow38, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check38 : integerHullCheck (integerOverlayPlanes ![3,5,10,8]) fractionRow38 = true := by decide
theorem vertices_fit38 (p : Point) (hp : p ∈ rationalHull rationalRow38) :
    ∀ g, ClosedCell ((![3,5,10,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow38_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check38 p hp
theorem fractionRow39_correct : fractionRow39.map FractionPoint.rational = rationalRow39 := by
  simp only [fractionRow39, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check39 : integerHullCheck (integerOverlayPlanes ![3,5,15,8]) fractionRow39 = true := by decide
theorem vertices_fit39 (p : Point) (hp : p ∈ rationalHull rationalRow39) :
    ∀ g, ClosedCell ((![3,5,15,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow39_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check39 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit32
