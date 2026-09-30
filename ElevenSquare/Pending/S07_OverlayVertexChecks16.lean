import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow128_correct : fractionRow128.map FractionPoint.rational = rationalRow128 := by
  simp only [fractionRow128, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check128 : integerHullCheck (integerOverlayPlanes ![9,6,5,2]) fractionRow128 = true := by decide
theorem vertices_fit128 (p : Point) (hp : p ∈ rationalHull rationalRow128) :
    ∀ g, ClosedCell ((![9,6,5,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow128_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check128 p hp
theorem fractionRow129_correct : fractionRow129.map FractionPoint.rational = rationalRow129 := by
  simp only [fractionRow129, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check129 : integerHullCheck (integerOverlayPlanes ![9,6,5,5]) fractionRow129 = true := by decide
theorem vertices_fit129 (p : Point) (hp : p ∈ rationalHull rationalRow129) :
    ∀ g, ClosedCell ((![9,6,5,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow129_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check129 p hp
theorem fractionRow130_correct : fractionRow130.map FractionPoint.rational = rationalRow130 := by
  simp only [fractionRow130, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check130 : integerHullCheck (integerOverlayPlanes ![9,6,5,6]) fractionRow130 = true := by decide
theorem vertices_fit130 (p : Point) (hp : p ∈ rationalHull rationalRow130) :
    ∀ g, ClosedCell ((![9,6,5,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow130_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check130 p hp
theorem fractionRow131_correct : fractionRow131.map FractionPoint.rational = rationalRow131 := by
  simp only [fractionRow131, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check131 : integerHullCheck (integerOverlayPlanes ![9,6,6,5]) fractionRow131 = true := by decide
theorem vertices_fit131 (p : Point) (hp : p ∈ rationalHull rationalRow131) :
    ∀ g, ClosedCell ((![9,6,6,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow131_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check131 p hp
theorem fractionRow132_correct : fractionRow132.map FractionPoint.rational = rationalRow132 := by
  simp only [fractionRow132, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check132 : integerHullCheck (integerOverlayPlanes ![9,6,6,6]) fractionRow132 = true := by decide
theorem vertices_fit132 (p : Point) (hp : p ∈ rationalHull rationalRow132) :
    ∀ g, ClosedCell ((![9,6,6,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow132_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check132 p hp
theorem fractionRow133_correct : fractionRow133.map FractionPoint.rational = rationalRow133 := by
  simp only [fractionRow133, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check133 : integerHullCheck (integerOverlayPlanes ![9,6,6,9]) fractionRow133 = true := by decide
theorem vertices_fit133 (p : Point) (hp : p ∈ rationalHull rationalRow133) :
    ∀ g, ClosedCell ((![9,6,6,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow133_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check133 p hp
theorem fractionRow134_correct : fractionRow134.map FractionPoint.rational = rationalRow134 := by
  simp only [fractionRow134, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check134 : integerHullCheck (integerOverlayPlanes ![9,6,9,6]) fractionRow134 = true := by decide
theorem vertices_fit134 (p : Point) (hp : p ∈ rationalHull rationalRow134) :
    ∀ g, ClosedCell ((![9,6,9,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow134_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check134 p hp
theorem fractionRow135_correct : fractionRow135.map FractionPoint.rational = rationalRow135 := by
  simp only [fractionRow135, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check135 : integerHullCheck (integerOverlayPlanes ![9,6,9,9]) fractionRow135 = true := by decide
theorem vertices_fit135 (p : Point) (hp : p ∈ rationalHull rationalRow135) :
    ∀ g, ClosedCell ((![9,6,9,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow135_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check135 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit128
