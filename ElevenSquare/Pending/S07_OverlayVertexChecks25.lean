import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow200_correct : fractionRow200.map FractionPoint.rational = rationalRow200 := by
  simp only [fractionRow200, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check200 : integerHullCheck (integerOverlayPlanes ![14,12,8,11]) fractionRow200 = true := by decide
theorem vertices_fit200 (p : Point) (hp : p ∈ rationalHull rationalRow200) :
    ∀ g, ClosedCell ((![14,12,8,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow200_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check200 p hp
theorem fractionRow201_correct : fractionRow201.map FractionPoint.rational = rationalRow201 := by
  simp only [fractionRow201, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check201 : integerHullCheck (integerOverlayPlanes ![14,12,8,15]) fractionRow201 = true := by decide
theorem vertices_fit201 (p : Point) (hp : p ∈ rationalHull rationalRow201) :
    ∀ g, ClosedCell ((![14,12,8,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow201_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check201 p hp
theorem fractionRow202_correct : fractionRow202.map FractionPoint.rational = rationalRow202 := by
  simp only [fractionRow202, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check202 : integerHullCheck (integerOverlayPlanes ![14,13,4,11]) fractionRow202 = true := by decide
theorem vertices_fit202 (p : Point) (hp : p ∈ rationalHull rationalRow202) :
    ∀ g, ClosedCell ((![14,13,4,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow202_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check202 p hp
theorem fractionRow203_correct : fractionRow203.map FractionPoint.rational = rationalRow203 := by
  simp only [fractionRow203, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check203 : integerHullCheck (integerOverlayPlanes ![14,13,8,11]) fractionRow203 = true := by decide
theorem vertices_fit203 (p : Point) (hp : p ∈ rationalHull rationalRow203) :
    ∀ g, ClosedCell ((![14,13,8,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow203_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check203 p hp
theorem fractionRow204_correct : fractionRow204.map FractionPoint.rational = rationalRow204 := by
  simp only [fractionRow204, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check204 : integerHullCheck (integerOverlayPlanes ![14,13,8,15]) fractionRow204 = true := by decide
theorem vertices_fit204 (p : Point) (hp : p ∈ rationalHull rationalRow204) :
    ∀ g, ClosedCell ((![14,13,8,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow204_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check204 p hp
theorem fractionRow205_correct : fractionRow205.map FractionPoint.rational = rationalRow205 := by
  simp only [fractionRow205, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check205 : integerHullCheck (integerOverlayPlanes ![14,14,4,7]) fractionRow205 = true := by decide
theorem vertices_fit205 (p : Point) (hp : p ∈ rationalHull rationalRow205) :
    ∀ g, ClosedCell ((![14,14,4,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow205_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check205 p hp
theorem fractionRow206_correct : fractionRow206.map FractionPoint.rational = rationalRow206 := by
  simp only [fractionRow206, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check206 : integerHullCheck (integerOverlayPlanes ![14,14,4,11]) fractionRow206 = true := by decide
theorem vertices_fit206 (p : Point) (hp : p ∈ rationalHull rationalRow206) :
    ∀ g, ClosedCell ((![14,14,4,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow206_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check206 p hp
theorem fractionRow207_correct : fractionRow207.map FractionPoint.rational = rationalRow207 := by
  simp only [fractionRow207, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check207 : integerHullCheck (integerOverlayPlanes ![14,14,8,11]) fractionRow207 = true := by decide
theorem vertices_fit207 (p : Point) (hp : p ∈ rationalHull rationalRow207) :
    ∀ g, ClosedCell ((![14,14,8,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow207_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check207 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit200
