import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow160_correct : fractionRow160.map FractionPoint.rational = rationalRow160 := by
  simp only [fractionRow160, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check160 : integerHullCheck (integerOverlayPlanes ![10,13,8,11]) fractionRow160 = true := by decide
theorem vertices_fit160 (p : Point) (hp : p ∈ rationalHull rationalRow160) :
    ∀ g, ClosedCell ((![10,13,8,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow160_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check160 p hp
theorem fractionRow161_correct : fractionRow161.map FractionPoint.rational = rationalRow161 := by
  simp only [fractionRow161, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check161 : integerHullCheck (integerOverlayPlanes ![10,13,8,15]) fractionRow161 = true := by decide
theorem vertices_fit161 (p : Point) (hp : p ∈ rationalHull rationalRow161) :
    ∀ g, ClosedCell ((![10,13,8,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow161_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check161 p hp
theorem fractionRow162_correct : fractionRow162.map FractionPoint.rational = rationalRow162 := by
  simp only [fractionRow162, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check162 : integerHullCheck (integerOverlayPlanes ![10,13,9,6]) fractionRow162 = true := by decide
theorem vertices_fit162 (p : Point) (hp : p ∈ rationalHull rationalRow162) :
    ∀ g, ClosedCell ((![10,13,9,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow162_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check162 p hp
theorem fractionRow163_correct : fractionRow163.map FractionPoint.rational = rationalRow163 := by
  simp only [fractionRow163, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check163 : integerHullCheck (integerOverlayPlanes ![10,13,9,10]) fractionRow163 = true := by decide
theorem vertices_fit163 (p : Point) (hp : p ∈ rationalHull rationalRow163) :
    ∀ g, ClosedCell ((![10,13,9,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow163_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check163 p hp
theorem fractionRow164_correct : fractionRow164.map FractionPoint.rational = rationalRow164 := by
  simp only [fractionRow164, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check164 : integerHullCheck (integerOverlayPlanes ![10,13,9,11]) fractionRow164 = true := by decide
theorem vertices_fit164 (p : Point) (hp : p ∈ rationalHull rationalRow164) :
    ∀ g, ClosedCell ((![10,13,9,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow164_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check164 p hp
theorem fractionRow165_correct : fractionRow165.map FractionPoint.rational = rationalRow165 := by
  simp only [fractionRow165, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check165 : integerHullCheck (integerOverlayPlanes ![10,13,13,10]) fractionRow165 = true := by decide
theorem vertices_fit165 (p : Point) (hp : p ∈ rationalHull rationalRow165) :
    ∀ g, ClosedCell ((![10,13,13,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow165_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check165 p hp
theorem fractionRow166_correct : fractionRow166.map FractionPoint.rational = rationalRow166 := by
  simp only [fractionRow166, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check166 : integerHullCheck (integerOverlayPlanes ![11,4,10,10]) fractionRow166 = true := by decide
theorem vertices_fit166 (p : Point) (hp : p ∈ rationalHull rationalRow166) :
    ∀ g, ClosedCell ((![11,4,10,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow166_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check166 p hp
theorem fractionRow167_correct : fractionRow167.map FractionPoint.rational = rationalRow167 := by
  simp only [fractionRow167, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check167 : integerHullCheck (integerOverlayPlanes ![11,4,10,13]) fractionRow167 = true := by decide
theorem vertices_fit167 (p : Point) (hp : p ∈ rationalHull rationalRow167) :
    ∀ g, ClosedCell ((![11,4,10,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow167_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check167 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit160
