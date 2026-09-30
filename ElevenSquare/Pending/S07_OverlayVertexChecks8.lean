import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow64_correct : fractionRow64.map FractionPoint.rational = rationalRow64 := by
  simp only [fractionRow64, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check64 : integerHullCheck (integerOverlayPlanes ![5,5,6,4]) fractionRow64 = true := by decide
theorem vertices_fit64 (p : Point) (hp : p ∈ rationalHull rationalRow64) :
    ∀ g, ClosedCell ((![5,5,6,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow64_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check64 p hp
theorem fractionRow65_correct : fractionRow65.map FractionPoint.rational = rationalRow65 := by
  simp only [fractionRow65, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check65 : integerHullCheck (integerOverlayPlanes ![5,5,6,9]) fractionRow65 = true := by decide
theorem vertices_fit65 (p : Point) (hp : p ∈ rationalHull rationalRow65) :
    ∀ g, ClosedCell ((![5,5,6,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow65_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check65 p hp
theorem fractionRow66_correct : fractionRow66.map FractionPoint.rational = rationalRow66 := by
  simp only [fractionRow66, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check66 : integerHullCheck (integerOverlayPlanes ![5,5,11,4]) fractionRow66 = true := by decide
theorem vertices_fit66 (p : Point) (hp : p ∈ rationalHull rationalRow66) :
    ∀ g, ClosedCell ((![5,5,11,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow66_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check66 p hp
theorem fractionRow67_correct : fractionRow67.map FractionPoint.rational = rationalRow67 := by
  simp only [fractionRow67, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check67 : integerHullCheck (integerOverlayPlanes ![5,5,11,9]) fractionRow67 = true := by decide
theorem vertices_fit67 (p : Point) (hp : p ∈ rationalHull rationalRow67) :
    ∀ g, ClosedCell ((![5,5,11,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow67_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check67 p hp
theorem fractionRow68_correct : fractionRow68.map FractionPoint.rational = rationalRow68 := by
  simp only [fractionRow68, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check68 : integerHullCheck (integerOverlayPlanes ![5,6,2,5]) fractionRow68 = true := by decide
theorem vertices_fit68 (p : Point) (hp : p ∈ rationalHull rationalRow68) :
    ∀ g, ClosedCell ((![5,6,2,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow68_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check68 p hp
theorem fractionRow69_correct : fractionRow69.map FractionPoint.rational = rationalRow69 := by
  simp only [fractionRow69, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check69 : integerHullCheck (integerOverlayPlanes ![5,6,6,5]) fractionRow69 = true := by decide
theorem vertices_fit69 (p : Point) (hp : p ∈ rationalHull rationalRow69) :
    ∀ g, ClosedCell ((![5,6,6,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow69_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check69 p hp
theorem fractionRow70_correct : fractionRow70.map FractionPoint.rational = rationalRow70 := by
  simp only [fractionRow70, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check70 : integerHullCheck (integerOverlayPlanes ![5,6,6,9]) fractionRow70 = true := by decide
theorem vertices_fit70 (p : Point) (hp : p ∈ rationalHull rationalRow70) :
    ∀ g, ClosedCell ((![5,6,6,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow70_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check70 p hp
theorem fractionRow71_correct : fractionRow71.map FractionPoint.rational = rationalRow71 := by
  simp only [fractionRow71, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check71 : integerHullCheck (integerOverlayPlanes ![5,7,2,5]) fractionRow71 = true := by decide
theorem vertices_fit71 (p : Point) (hp : p ∈ rationalHull rationalRow71) :
    ∀ g, ClosedCell ((![5,7,2,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow71_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check71 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit64
