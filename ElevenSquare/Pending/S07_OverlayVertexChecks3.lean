import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow24_correct : fractionRow24.map FractionPoint.rational = rationalRow24 := by
  simp only [fractionRow24, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check24 : integerHullCheck (integerOverlayPlanes ![2,1,15,8]) fractionRow24 = true := by decide
theorem vertices_fit24 (p : Point) (hp : p ∈ rationalHull rationalRow24) :
    ∀ g, ClosedCell ((![2,1,15,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow24_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check24 p hp
theorem fractionRow25_correct : fractionRow25.map FractionPoint.rational = rationalRow25 := by
  simp only [fractionRow25, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check25 : integerHullCheck (integerOverlayPlanes ![2,2,11,4]) fractionRow25 = true := by decide
theorem vertices_fit25 (p : Point) (hp : p ∈ rationalHull rationalRow25) :
    ∀ g, ClosedCell ((![2,2,11,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow25_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check25 p hp
theorem fractionRow26_correct : fractionRow26.map FractionPoint.rational = rationalRow26 := by
  simp only [fractionRow26, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check26 : integerHullCheck (integerOverlayPlanes ![2,5,6,9]) fractionRow26 = true := by decide
theorem vertices_fit26 (p : Point) (hp : p ∈ rationalHull rationalRow26) :
    ∀ g, ClosedCell ((![2,5,6,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow26_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check26 p hp
theorem fractionRow27_correct : fractionRow27.map FractionPoint.rational = rationalRow27 := by
  simp only [fractionRow27, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check27 : integerHullCheck (integerOverlayPlanes ![2,5,10,8]) fractionRow27 = true := by decide
theorem vertices_fit27 (p : Point) (hp : p ∈ rationalHull rationalRow27) :
    ∀ g, ClosedCell ((![2,5,10,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow27_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check27 p hp
theorem fractionRow28_correct : fractionRow28.map FractionPoint.rational = rationalRow28 := by
  simp only [fractionRow28, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check28 : integerHullCheck (integerOverlayPlanes ![2,5,10,9]) fractionRow28 = true := by decide
theorem vertices_fit28 (p : Point) (hp : p ∈ rationalHull rationalRow28) :
    ∀ g, ClosedCell ((![2,5,10,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow28_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check28 p hp
theorem fractionRow29_correct : fractionRow29.map FractionPoint.rational = rationalRow29 := by
  simp only [fractionRow29, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check29 : integerHullCheck (integerOverlayPlanes ![2,5,10,13]) fractionRow29 = true := by decide
theorem vertices_fit29 (p : Point) (hp : p ∈ rationalHull rationalRow29) :
    ∀ g, ClosedCell ((![2,5,10,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow29_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check29 p hp
theorem fractionRow30_correct : fractionRow30.map FractionPoint.rational = rationalRow30 := by
  simp only [fractionRow30, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check30 : integerHullCheck (integerOverlayPlanes ![2,5,11,4]) fractionRow30 = true := by decide
theorem vertices_fit30 (p : Point) (hp : p ∈ rationalHull rationalRow30) :
    ∀ g, ClosedCell ((![2,5,11,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow30_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check30 p hp
theorem fractionRow31_correct : fractionRow31.map FractionPoint.rational = rationalRow31 := by
  simp only [fractionRow31, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check31 : integerHullCheck (integerOverlayPlanes ![2,5,11,8]) fractionRow31 = true := by decide
theorem vertices_fit31 (p : Point) (hp : p ∈ rationalHull rationalRow31) :
    ∀ g, ClosedCell ((![2,5,11,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow31_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check31 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit24
