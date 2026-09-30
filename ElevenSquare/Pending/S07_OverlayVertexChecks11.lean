import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow88_correct : fractionRow88.map FractionPoint.rational = rationalRow88 := by
  simp only [fractionRow88, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check88 : integerHullCheck (integerOverlayPlanes ![6,9,9,10]) fractionRow88 = true := by decide
theorem vertices_fit88 (p : Point) (hp : p ∈ rationalHull rationalRow88) :
    ∀ g, ClosedCell ((![6,9,9,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow88_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check88 p hp
theorem fractionRow89_correct : fractionRow89.map FractionPoint.rational = rationalRow89 := by
  simp only [fractionRow89, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check89 : integerHullCheck (integerOverlayPlanes ![6,9,10,9]) fractionRow89 = true := by decide
theorem vertices_fit89 (p : Point) (hp : p ∈ rationalHull rationalRow89) :
    ∀ g, ClosedCell ((![6,9,10,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow89_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check89 p hp
theorem fractionRow90_correct : fractionRow90.map FractionPoint.rational = rationalRow90 := by
  simp only [fractionRow90, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check90 : integerHullCheck (integerOverlayPlanes ![6,9,10,10]) fractionRow90 = true := by decide
theorem vertices_fit90 (p : Point) (hp : p ∈ rationalHull rationalRow90) :
    ∀ g, ClosedCell ((![6,9,10,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow90_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check90 p hp
theorem fractionRow91_correct : fractionRow91.map FractionPoint.rational = rationalRow91 := by
  simp only [fractionRow91, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check91 : integerHullCheck (integerOverlayPlanes ![6,9,10,13]) fractionRow91 = true := by decide
theorem vertices_fit91 (p : Point) (hp : p ∈ rationalHull rationalRow91) :
    ∀ g, ClosedCell ((![6,9,10,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow91_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check91 p hp
theorem fractionRow92_correct : fractionRow92.map FractionPoint.rational = rationalRow92 := by
  simp only [fractionRow92, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check92 : integerHullCheck (integerOverlayPlanes ![6,9,13,10]) fractionRow92 = true := by decide
theorem vertices_fit92 (p : Point) (hp : p ∈ rationalHull rationalRow92) :
    ∀ g, ClosedCell ((![6,9,13,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow92_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check92 p hp
theorem fractionRow93_correct : fractionRow93.map FractionPoint.rational = rationalRow93 := by
  simp only [fractionRow93, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check93 : integerHullCheck (integerOverlayPlanes ![7,0,10,8]) fractionRow93 = true := by decide
theorem vertices_fit93 (p : Point) (hp : p ∈ rationalHull rationalRow93) :
    ∀ g, ClosedCell ((![7,0,10,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow93_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check93 p hp
theorem fractionRow94_correct : fractionRow94.map FractionPoint.rational = rationalRow94 := by
  simp only [fractionRow94, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check94 : integerHullCheck (integerOverlayPlanes ![7,0,10,12]) fractionRow94 = true := by decide
theorem vertices_fit94 (p : Point) (hp : p ∈ rationalHull rationalRow94) :
    ∀ g, ClosedCell ((![7,0,10,12] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow94_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check94 p hp
theorem fractionRow95_correct : fractionRow95.map FractionPoint.rational = rationalRow95 := by
  simp only [fractionRow95, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check95 : integerHullCheck (integerOverlayPlanes ![7,0,10,13]) fractionRow95 = true := by decide
theorem vertices_fit95 (p : Point) (hp : p ∈ rationalHull rationalRow95) :
    ∀ g, ClosedCell ((![7,0,10,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow95_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check95 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit88
