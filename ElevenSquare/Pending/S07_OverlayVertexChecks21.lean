import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow168_correct : fractionRow168.map FractionPoint.rational = rationalRow168 := by
  simp only [fractionRow168, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check168 : integerHullCheck (integerOverlayPlanes ![11,4,13,10]) fractionRow168 = true := by decide
theorem vertices_fit168 (p : Point) (hp : p ∈ rationalHull rationalRow168) :
    ∀ g, ClosedCell ((![11,4,13,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow168_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check168 p hp
theorem fractionRow169_correct : fractionRow169.map FractionPoint.rational = rationalRow169 := by
  simp only [fractionRow169, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check169 : integerHullCheck (integerOverlayPlanes ![11,4,13,13]) fractionRow169 = true := by decide
theorem vertices_fit169 (p : Point) (hp : p ∈ rationalHull rationalRow169) :
    ∀ g, ClosedCell ((![11,4,13,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow169_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check169 p hp
theorem fractionRow170_correct : fractionRow170.map FractionPoint.rational = rationalRow170 := by
  simp only [fractionRow170, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check170 : integerHullCheck (integerOverlayPlanes ![11,4,13,14]) fractionRow170 = true := by decide
theorem vertices_fit170 (p : Point) (hp : p ∈ rationalHull rationalRow170) :
    ∀ g, ClosedCell ((![11,4,13,14] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow170_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check170 p hp
theorem fractionRow171_correct : fractionRow171.map FractionPoint.rational = rationalRow171 := by
  simp only [fractionRow171, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check171 : integerHullCheck (integerOverlayPlanes ![11,4,14,13]) fractionRow171 = true := by decide
theorem vertices_fit171 (p : Point) (hp : p ∈ rationalHull rationalRow171) :
    ∀ g, ClosedCell ((![11,4,14,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow171_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check171 p hp
theorem fractionRow172_correct : fractionRow172.map FractionPoint.rational = rationalRow172 := by
  simp only [fractionRow172, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check172 : integerHullCheck (integerOverlayPlanes ![11,4,14,14]) fractionRow172 = true := by decide
theorem vertices_fit172 (p : Point) (hp : p ∈ rationalHull rationalRow172) :
    ∀ g, ClosedCell ((![11,4,14,14] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow172_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check172 p hp
theorem fractionRow173_correct : fractionRow173.map FractionPoint.rational = rationalRow173 := by
  simp only [fractionRow173, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check173 : integerHullCheck (integerOverlayPlanes ![11,8,12,14]) fractionRow173 = true := by decide
theorem vertices_fit173 (p : Point) (hp : p ∈ rationalHull rationalRow173) :
    ∀ g, ClosedCell ((![11,8,12,14] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow173_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check173 p hp
theorem fractionRow174_correct : fractionRow174.map FractionPoint.rational = rationalRow174 := by
  simp only [fractionRow174, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check174 : integerHullCheck (integerOverlayPlanes ![11,8,13,10]) fractionRow174 = true := by decide
theorem vertices_fit174 (p : Point) (hp : p ∈ rationalHull rationalRow174) :
    ∀ g, ClosedCell ((![11,8,13,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow174_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check174 p hp
theorem fractionRow175_correct : fractionRow175.map FractionPoint.rational = rationalRow175 := by
  simp only [fractionRow175, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check175 : integerHullCheck (integerOverlayPlanes ![11,8,13,14]) fractionRow175 = true := by decide
theorem vertices_fit175 (p : Point) (hp : p ∈ rationalHull rationalRow175) :
    ∀ g, ClosedCell ((![11,8,13,14] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow175_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check175 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit168
