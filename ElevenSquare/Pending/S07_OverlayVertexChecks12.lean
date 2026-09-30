import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow96_correct : fractionRow96.map FractionPoint.rational = rationalRow96 := by
  simp only [fractionRow96, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check96 : integerHullCheck (integerOverlayPlanes ![7,0,14,12]) fractionRow96 = true := by decide
theorem vertices_fit96 (p : Point) (hp : p ∈ rationalHull rationalRow96) :
    ∀ g, ClosedCell ((![7,0,14,12] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow96_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check96 p hp
theorem fractionRow97_correct : fractionRow97.map FractionPoint.rational = rationalRow97 := by
  simp only [fractionRow97, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check97 : integerHullCheck (integerOverlayPlanes ![7,0,14,13]) fractionRow97 = true := by decide
theorem vertices_fit97 (p : Point) (hp : p ∈ rationalHull rationalRow97) :
    ∀ g, ClosedCell ((![7,0,14,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow97_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check97 p hp
theorem fractionRow98_correct : fractionRow98.map FractionPoint.rational = rationalRow98 := by
  simp only [fractionRow98, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check98 : integerHullCheck (integerOverlayPlanes ![7,0,15,8]) fractionRow98 = true := by decide
theorem vertices_fit98 (p : Point) (hp : p ∈ rationalHull rationalRow98) :
    ∀ g, ClosedCell ((![7,0,15,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow98_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check98 p hp
theorem fractionRow99_correct : fractionRow99.map FractionPoint.rational = rationalRow99 := by
  simp only [fractionRow99, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check99 : integerHullCheck (integerOverlayPlanes ![7,0,15,12]) fractionRow99 = true := by decide
theorem vertices_fit99 (p : Point) (hp : p ∈ rationalHull rationalRow99) :
    ∀ g, ClosedCell ((![7,0,15,12] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow99_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check99 p hp
theorem fractionRow100_correct : fractionRow100.map FractionPoint.rational = rationalRow100 := by
  simp only [fractionRow100, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check100 : integerHullCheck (integerOverlayPlanes ![7,0,15,13]) fractionRow100 = true := by decide
theorem vertices_fit100 (p : Point) (hp : p ∈ rationalHull rationalRow100) :
    ∀ g, ClosedCell ((![7,0,15,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow100_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check100 p hp
theorem fractionRow101_correct : fractionRow101.map FractionPoint.rational = rationalRow101 := by
  simp only [fractionRow101, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check101 : integerHullCheck (integerOverlayPlanes ![7,4,10,13]) fractionRow101 = true := by decide
theorem vertices_fit101 (p : Point) (hp : p ∈ rationalHull rationalRow101) :
    ∀ g, ClosedCell ((![7,4,10,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow101_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check101 p hp
theorem fractionRow102_correct : fractionRow102.map FractionPoint.rational = rationalRow102 := by
  simp only [fractionRow102, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check102 : integerHullCheck (integerOverlayPlanes ![7,4,14,12]) fractionRow102 = true := by decide
theorem vertices_fit102 (p : Point) (hp : p ∈ rationalHull rationalRow102) :
    ∀ g, ClosedCell ((![7,4,14,12] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow102_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check102 p hp
theorem fractionRow103_correct : fractionRow103.map FractionPoint.rational = rationalRow103 := by
  simp only [fractionRow103, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check103 : integerHullCheck (integerOverlayPlanes ![7,4,14,13]) fractionRow103 = true := by decide
theorem vertices_fit103 (p : Point) (hp : p ∈ rationalHull rationalRow103) :
    ∀ g, ClosedCell ((![7,4,14,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow103_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check103 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit96
