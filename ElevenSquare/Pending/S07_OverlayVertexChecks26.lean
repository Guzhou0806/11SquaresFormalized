import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow208_correct : fractionRow208.map FractionPoint.rational = rationalRow208 := by
  simp only [fractionRow208, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check208 : integerHullCheck (integerOverlayPlanes ![15,8,8,10]) fractionRow208 = true := by decide
theorem vertices_fit208 (p : Point) (hp : p ∈ rationalHull rationalRow208) :
    ∀ g, ClosedCell ((![15,8,8,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow208_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check208 p hp
theorem fractionRow209_correct : fractionRow209.map FractionPoint.rational = rationalRow209 := by
  simp only [fractionRow209, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check209 : integerHullCheck (integerOverlayPlanes ![15,8,8,15]) fractionRow209 = true := by decide
theorem vertices_fit209 (p : Point) (hp : p ∈ rationalHull rationalRow209) :
    ∀ g, ClosedCell ((![15,8,8,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow209_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check209 p hp
theorem fractionRow210_correct : fractionRow210.map FractionPoint.rational = rationalRow210 := by
  simp only [fractionRow210, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check210 : integerHullCheck (integerOverlayPlanes ![15,8,12,10]) fractionRow210 = true := by decide
theorem vertices_fit210 (p : Point) (hp : p ∈ rationalHull rationalRow210) :
    ∀ g, ClosedCell ((![15,8,12,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow210_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check210 p hp
theorem fractionRow211_correct : fractionRow211.map FractionPoint.rational = rationalRow211 := by
  simp only [fractionRow211, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check211 : integerHullCheck (integerOverlayPlanes ![15,8,12,14]) fractionRow211 = true := by decide
theorem vertices_fit211 (p : Point) (hp : p ∈ rationalHull rationalRow211) :
    ∀ g, ClosedCell ((![15,8,12,14] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow211_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check211 p hp
theorem fractionRow212_correct : fractionRow212.map FractionPoint.rational = rationalRow212 := by
  simp only [fractionRow212, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check212 : integerHullCheck (integerOverlayPlanes ![15,8,12,15]) fractionRow212 = true := by decide
theorem vertices_fit212 (p : Point) (hp : p ∈ rationalHull rationalRow212) :
    ∀ g, ClosedCell ((![15,8,12,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow212_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check212 p hp
theorem fractionRow213_correct : fractionRow213.map FractionPoint.rational = rationalRow213 := by
  simp only [fractionRow213, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check213 : integerHullCheck (integerOverlayPlanes ![15,8,13,10]) fractionRow213 = true := by decide
theorem vertices_fit213 (p : Point) (hp : p ∈ rationalHull rationalRow213) :
    ∀ g, ClosedCell ((![15,8,13,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow213_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check213 p hp
theorem fractionRow214_correct : fractionRow214.map FractionPoint.rational = rationalRow214 := by
  simp only [fractionRow214, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check214 : integerHullCheck (integerOverlayPlanes ![15,8,13,14]) fractionRow214 = true := by decide
theorem vertices_fit214 (p : Point) (hp : p ∈ rationalHull rationalRow214) :
    ∀ g, ClosedCell ((![15,8,13,14] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow214_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check214 p hp
theorem fractionRow215_correct : fractionRow215.map FractionPoint.rational = rationalRow215 := by
  simp only [fractionRow215, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check215 : integerHullCheck (integerOverlayPlanes ![15,8,13,15]) fractionRow215 = true := by decide
theorem vertices_fit215 (p : Point) (hp : p ∈ rationalHull rationalRow215) :
    ∀ g, ClosedCell ((![15,8,13,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow215_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check215 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit208
