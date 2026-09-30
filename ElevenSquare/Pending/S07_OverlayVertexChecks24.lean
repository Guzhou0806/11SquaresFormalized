import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow192_correct : fractionRow192.map FractionPoint.rational = rationalRow192 := by
  simp only [fractionRow192, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check192 : integerHullCheck (integerOverlayPlanes ![13,10,5,7]) fractionRow192 = true := by decide
theorem vertices_fit192 (p : Point) (hp : p ∈ rationalHull rationalRow192) :
    ∀ g, ClosedCell ((![13,10,5,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow192_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check192 p hp
theorem fractionRow193_correct : fractionRow193.map FractionPoint.rational = rationalRow193 := by
  simp only [fractionRow193, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check193 : integerHullCheck (integerOverlayPlanes ![13,10,9,6]) fractionRow193 = true := by decide
theorem vertices_fit193 (p : Point) (hp : p ∈ rationalHull rationalRow193) :
    ∀ g, ClosedCell ((![13,10,9,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow193_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check193 p hp
theorem fractionRow194_correct : fractionRow194.map FractionPoint.rational = rationalRow194 := by
  simp only [fractionRow194, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check194 : integerHullCheck (integerOverlayPlanes ![13,13,4,11]) fractionRow194 = true := by decide
theorem vertices_fit194 (p : Point) (hp : p ∈ rationalHull rationalRow194) :
    ∀ g, ClosedCell ((![13,13,4,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow194_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check194 p hp
theorem fractionRow195_correct : fractionRow195.map FractionPoint.rational = rationalRow195 := by
  simp only [fractionRow195, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check195 : integerHullCheck (integerOverlayPlanes ![13,14,0,7]) fractionRow195 = true := by decide
theorem vertices_fit195 (p : Point) (hp : p ∈ rationalHull rationalRow195) :
    ∀ g, ClosedCell ((![13,14,0,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow195_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check195 p hp
theorem fractionRow196_correct : fractionRow196.map FractionPoint.rational = rationalRow196 := by
  simp only [fractionRow196, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check196 : integerHullCheck (integerOverlayPlanes ![13,14,4,7]) fractionRow196 = true := by decide
theorem vertices_fit196 (p : Point) (hp : p ∈ rationalHull rationalRow196) :
    ∀ g, ClosedCell ((![13,14,4,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow196_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check196 p hp
theorem fractionRow197_correct : fractionRow197.map FractionPoint.rational = rationalRow197 := by
  simp only [fractionRow197, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check197 : integerHullCheck (integerOverlayPlanes ![13,14,4,11]) fractionRow197 = true := by decide
theorem vertices_fit197 (p : Point) (hp : p ∈ rationalHull rationalRow197) :
    ∀ g, ClosedCell ((![13,14,4,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow197_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check197 p hp
theorem fractionRow198_correct : fractionRow198.map FractionPoint.rational = rationalRow198 := by
  simp only [fractionRow198, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check198 : integerHullCheck (integerOverlayPlanes ![13,15,0,7]) fractionRow198 = true := by decide
theorem vertices_fit198 (p : Point) (hp : p ∈ rationalHull rationalRow198) :
    ∀ g, ClosedCell ((![13,15,0,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow198_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check198 p hp
theorem fractionRow199_correct : fractionRow199.map FractionPoint.rational = rationalRow199 := by
  simp only [fractionRow199, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check199 : integerHullCheck (integerOverlayPlanes ![13,15,4,7]) fractionRow199 = true := by decide
theorem vertices_fit199 (p : Point) (hp : p ∈ rationalHull rationalRow199) :
    ∀ g, ClosedCell ((![13,15,4,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow199_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check199 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit192
