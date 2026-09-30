import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow48_correct : fractionRow48.map FractionPoint.rational = rationalRow48 := by
  simp only [fractionRow48, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check48 : integerHullCheck (integerOverlayPlanes ![4,11,1,2]) fractionRow48 = true := by decide
theorem vertices_fit48 (p : Point) (hp : p ∈ rationalHull rationalRow48) :
    ∀ g, ClosedCell ((![4,11,1,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow48_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check48 p hp
theorem fractionRow49_correct : fractionRow49.map FractionPoint.rational = rationalRow49 := by
  simp only [fractionRow49, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check49 : integerHullCheck (integerOverlayPlanes ![4,11,2,1]) fractionRow49 = true := by decide
theorem vertices_fit49 (p : Point) (hp : p ∈ rationalHull rationalRow49) :
    ∀ g, ClosedCell ((![4,11,2,1] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow49_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check49 p hp
theorem fractionRow50_correct : fractionRow50.map FractionPoint.rational = rationalRow50 := by
  simp only [fractionRow50, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check50 : integerHullCheck (integerOverlayPlanes ![4,11,2,2]) fractionRow50 = true := by decide
theorem vertices_fit50 (p : Point) (hp : p ∈ rationalHull rationalRow50) :
    ∀ g, ClosedCell ((![4,11,2,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow50_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check50 p hp
theorem fractionRow51_correct : fractionRow51.map FractionPoint.rational = rationalRow51 := by
  simp only [fractionRow51, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check51 : integerHullCheck (integerOverlayPlanes ![4,11,2,5]) fractionRow51 = true := by decide
theorem vertices_fit51 (p : Point) (hp : p ∈ rationalHull rationalRow51) :
    ∀ g, ClosedCell ((![4,11,2,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow51_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check51 p hp
theorem fractionRow52_correct : fractionRow52.map FractionPoint.rational = rationalRow52 := by
  simp only [fractionRow52, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check52 : integerHullCheck (integerOverlayPlanes ![4,11,5,2]) fractionRow52 = true := by decide
theorem vertices_fit52 (p : Point) (hp : p ∈ rationalHull rationalRow52) :
    ∀ g, ClosedCell ((![4,11,5,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow52_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check52 p hp
theorem fractionRow53_correct : fractionRow53.map FractionPoint.rational = rationalRow53 := by
  simp only [fractionRow53, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check53 : integerHullCheck (integerOverlayPlanes ![4,11,5,5]) fractionRow53 = true := by decide
theorem vertices_fit53 (p : Point) (hp : p ∈ rationalHull rationalRow53) :
    ∀ g, ClosedCell ((![4,11,5,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow53_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check53 p hp
theorem fractionRow54_correct : fractionRow54.map FractionPoint.rational = rationalRow54 := by
  simp only [fractionRow54, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check54 : integerHullCheck (integerOverlayPlanes ![5,2,2,5]) fractionRow54 = true := by decide
theorem vertices_fit54 (p : Point) (hp : p ∈ rationalHull rationalRow54) :
    ∀ g, ClosedCell ((![5,2,2,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow54_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check54 p hp
theorem fractionRow55_correct : fractionRow55.map FractionPoint.rational = rationalRow55 := by
  simp only [fractionRow55, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check55 : integerHullCheck (integerOverlayPlanes ![5,2,6,4]) fractionRow55 = true := by decide
theorem vertices_fit55 (p : Point) (hp : p ∈ rationalHull rationalRow55) :
    ∀ g, ClosedCell ((![5,2,6,4] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow55_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check55 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit48
