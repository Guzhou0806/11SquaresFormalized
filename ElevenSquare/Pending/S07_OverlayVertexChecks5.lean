import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow40_correct : fractionRow40.map FractionPoint.rational = rationalRow40 := by
  simp only [fractionRow40, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check40 : integerHullCheck (integerOverlayPlanes ![4,6,2,5]) fractionRow40 = true := by decide
theorem vertices_fit40 (p : Point) (hp : p ∈ rationalHull rationalRow40) :
    ∀ g, ClosedCell ((![4,6,2,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow40_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check40 p hp
theorem fractionRow41_correct : fractionRow41.map FractionPoint.rational = rationalRow41 := by
  simp only [fractionRow41, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check41 : integerHullCheck (integerOverlayPlanes ![4,6,5,5]) fractionRow41 = true := by decide
theorem vertices_fit41 (p : Point) (hp : p ∈ rationalHull rationalRow41) :
    ∀ g, ClosedCell ((![4,6,5,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow41_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check41 p hp
theorem fractionRow42_correct : fractionRow42.map FractionPoint.rational = rationalRow42 := by
  simp only [fractionRow42, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check42 : integerHullCheck (integerOverlayPlanes ![4,7,1,1]) fractionRow42 = true := by decide
theorem vertices_fit42 (p : Point) (hp : p ∈ rationalHull rationalRow42) :
    ∀ g, ClosedCell ((![4,7,1,1] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow42_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check42 p hp
theorem fractionRow43_correct : fractionRow43.map FractionPoint.rational = rationalRow43 := by
  simp only [fractionRow43, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check43 : integerHullCheck (integerOverlayPlanes ![4,7,2,0]) fractionRow43 = true := by decide
theorem vertices_fit43 (p : Point) (hp : p ∈ rationalHull rationalRow43) :
    ∀ g, ClosedCell ((![4,7,2,0] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow43_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check43 p hp
theorem fractionRow44_correct : fractionRow44.map FractionPoint.rational = rationalRow44 := by
  simp only [fractionRow44, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check44 : integerHullCheck (integerOverlayPlanes ![4,7,2,1]) fractionRow44 = true := by decide
theorem vertices_fit44 (p : Point) (hp : p ∈ rationalHull rationalRow44) :
    ∀ g, ClosedCell ((![4,7,2,1] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow44_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check44 p hp
theorem fractionRow45_correct : fractionRow45.map FractionPoint.rational = rationalRow45 := by
  simp only [fractionRow45, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check45 : integerHullCheck (integerOverlayPlanes ![4,7,2,5]) fractionRow45 = true := by decide
theorem vertices_fit45 (p : Point) (hp : p ∈ rationalHull rationalRow45) :
    ∀ g, ClosedCell ((![4,7,2,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow45_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check45 p hp
theorem fractionRow46_correct : fractionRow46.map FractionPoint.rational = rationalRow46 := by
  simp only [fractionRow46, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check46 : integerHullCheck (integerOverlayPlanes ![4,7,3,1]) fractionRow46 = true := by decide
theorem vertices_fit46 (p : Point) (hp : p ∈ rationalHull rationalRow46) :
    ∀ g, ClosedCell ((![4,7,3,1] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow46_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check46 p hp
theorem fractionRow47_correct : fractionRow47.map FractionPoint.rational = rationalRow47 := by
  simp only [fractionRow47, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check47 : integerHullCheck (integerOverlayPlanes ![4,11,1,1]) fractionRow47 = true := by decide
theorem vertices_fit47 (p : Point) (hp : p ∈ rationalHull rationalRow47) :
    ∀ g, ClosedCell ((![4,11,1,1] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow47_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check47 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit40
