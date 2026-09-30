import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow152_correct : fractionRow152.map FractionPoint.rational = rationalRow152 := by
  simp only [fractionRow152, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check152 : integerHullCheck (integerOverlayPlanes ![10,10,4,6]) fractionRow152 = true := by decide
theorem vertices_fit152 (p : Point) (hp : p ∈ rationalHull rationalRow152) :
    ∀ g, ClosedCell ((![10,10,4,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow152_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check152 p hp
theorem fractionRow153_correct : fractionRow153.map FractionPoint.rational = rationalRow153 := by
  simp only [fractionRow153, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check153 : integerHullCheck (integerOverlayPlanes ![10,10,4,11]) fractionRow153 = true := by decide
theorem vertices_fit153 (p : Point) (hp : p ∈ rationalHull rationalRow153) :
    ∀ g, ClosedCell ((![10,10,4,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow153_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check153 p hp
theorem fractionRow154_correct : fractionRow154.map FractionPoint.rational = rationalRow154 := by
  simp only [fractionRow154, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check154 : integerHullCheck (integerOverlayPlanes ![10,10,9,6]) fractionRow154 = true := by decide
theorem vertices_fit154 (p : Point) (hp : p ∈ rationalHull rationalRow154) :
    ∀ g, ClosedCell ((![10,10,9,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow154_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check154 p hp
theorem fractionRow155_correct : fractionRow155.map FractionPoint.rational = rationalRow155 := by
  simp only [fractionRow155, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check155 : integerHullCheck (integerOverlayPlanes ![10,10,9,11]) fractionRow155 = true := by decide
theorem vertices_fit155 (p : Point) (hp : p ∈ rationalHull rationalRow155) :
    ∀ g, ClosedCell ((![10,10,9,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow155_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check155 p hp
theorem fractionRow156_correct : fractionRow156.map FractionPoint.rational = rationalRow156 := by
  simp only [fractionRow156, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check156 : integerHullCheck (integerOverlayPlanes ![10,12,8,10]) fractionRow156 = true := by decide
theorem vertices_fit156 (p : Point) (hp : p ∈ rationalHull rationalRow156) :
    ∀ g, ClosedCell ((![10,12,8,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow156_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check156 p hp
theorem fractionRow157_correct : fractionRow157.map FractionPoint.rational = rationalRow157 := by
  simp only [fractionRow157, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check157 : integerHullCheck (integerOverlayPlanes ![10,12,8,15]) fractionRow157 = true := by decide
theorem vertices_fit157 (p : Point) (hp : p ∈ rationalHull rationalRow157) :
    ∀ g, ClosedCell ((![10,12,8,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow157_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check157 p hp
theorem fractionRow158_correct : fractionRow158.map FractionPoint.rational = rationalRow158 := by
  simp only [fractionRow158, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check158 : integerHullCheck (integerOverlayPlanes ![10,13,4,11]) fractionRow158 = true := by decide
theorem vertices_fit158 (p : Point) (hp : p ∈ rationalHull rationalRow158) :
    ∀ g, ClosedCell ((![10,13,4,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow158_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check158 p hp
theorem fractionRow159_correct : fractionRow159.map FractionPoint.rational = rationalRow159 := by
  simp only [fractionRow159, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check159 : integerHullCheck (integerOverlayPlanes ![10,13,8,10]) fractionRow159 = true := by decide
theorem vertices_fit159 (p : Point) (hp : p ∈ rationalHull rationalRow159) :
    ∀ g, ClosedCell ((![10,13,8,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow159_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check159 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit152
