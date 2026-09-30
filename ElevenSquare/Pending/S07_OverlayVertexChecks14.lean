import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow112_correct : fractionRow112.map FractionPoint.rational = rationalRow112 := by
  simp only [fractionRow112, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check112 : integerHullCheck (integerOverlayPlanes ![8,10,5,3]) fractionRow112 = true := by decide
theorem vertices_fit112 (p : Point) (hp : p ∈ rationalHull rationalRow112) :
    ∀ g, ClosedCell ((![8,10,5,3] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow112_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check112 p hp
theorem fractionRow113_correct : fractionRow113.map FractionPoint.rational = rationalRow113 := by
  simp only [fractionRow113, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check113 : integerHullCheck (integerOverlayPlanes ![8,10,5,7]) fractionRow113 = true := by decide
theorem vertices_fit113 (p : Point) (hp : p ∈ rationalHull rationalRow113) :
    ∀ g, ClosedCell ((![8,10,5,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow113_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check113 p hp
theorem fractionRow114_correct : fractionRow114.map FractionPoint.rational = rationalRow114 := by
  simp only [fractionRow114, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check114 : integerHullCheck (integerOverlayPlanes ![8,11,0,2]) fractionRow114 = true := by decide
theorem vertices_fit114 (p : Point) (hp : p ∈ rationalHull rationalRow114) :
    ∀ g, ClosedCell ((![8,11,0,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow114_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check114 p hp
theorem fractionRow115_correct : fractionRow115.map FractionPoint.rational = rationalRow115 := by
  simp only [fractionRow115, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check115 : integerHullCheck (integerOverlayPlanes ![8,11,1,1]) fractionRow115 = true := by decide
theorem vertices_fit115 (p : Point) (hp : p ∈ rationalHull rationalRow115) :
    ∀ g, ClosedCell ((![8,11,1,1] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow115_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check115 p hp
theorem fractionRow116_correct : fractionRow116.map FractionPoint.rational = rationalRow116 := by
  simp only [fractionRow116, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check116 : integerHullCheck (integerOverlayPlanes ![8,11,1,2]) fractionRow116 = true := by decide
theorem vertices_fit116 (p : Point) (hp : p ∈ rationalHull rationalRow116) :
    ∀ g, ClosedCell ((![8,11,1,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow116_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check116 p hp
theorem fractionRow117_correct : fractionRow117.map FractionPoint.rational = rationalRow117 := by
  simp only [fractionRow117, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check117 : integerHullCheck (integerOverlayPlanes ![8,11,1,3]) fractionRow117 = true := by decide
theorem vertices_fit117 (p : Point) (hp : p ∈ rationalHull rationalRow117) :
    ∀ g, ClosedCell ((![8,11,1,3] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow117_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check117 p hp
theorem fractionRow118_correct : fractionRow118.map FractionPoint.rational = rationalRow118 := by
  simp only [fractionRow118, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check118 : integerHullCheck (integerOverlayPlanes ![8,11,5,2]) fractionRow118 = true := by decide
theorem vertices_fit118 (p : Point) (hp : p ∈ rationalHull rationalRow118) :
    ∀ g, ClosedCell ((![8,11,5,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow118_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check118 p hp
theorem fractionRow119_correct : fractionRow119.map FractionPoint.rational = rationalRow119 := by
  simp only [fractionRow119, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check119 : integerHullCheck (integerOverlayPlanes ![8,15,0,2]) fractionRow119 = true := by decide
theorem vertices_fit119 (p : Point) (hp : p ∈ rationalHull rationalRow119) :
    ∀ g, ClosedCell ((![8,15,0,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow119_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check119 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit112
