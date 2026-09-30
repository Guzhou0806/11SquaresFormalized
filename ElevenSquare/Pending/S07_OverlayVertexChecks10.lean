import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow80_correct : fractionRow80.map FractionPoint.rational = rationalRow80 := by
  simp only [fractionRow80, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check80 : integerHullCheck (integerOverlayPlanes ![6,6,6,6]) fractionRow80 = true := by decide
theorem vertices_fit80 (p : Point) (hp : p ∈ rationalHull rationalRow80) :
    ∀ g, ClosedCell ((![6,6,6,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow80_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check80 p hp
theorem fractionRow81_correct : fractionRow81.map FractionPoint.rational = rationalRow81 := by
  simp only [fractionRow81, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check81 : integerHullCheck (integerOverlayPlanes ![6,6,6,9]) fractionRow81 = true := by decide
theorem vertices_fit81 (p : Point) (hp : p ∈ rationalHull rationalRow81) :
    ∀ g, ClosedCell ((![6,6,6,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow81_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check81 p hp
theorem fractionRow82_correct : fractionRow82.map FractionPoint.rational = rationalRow82 := by
  simp only [fractionRow82, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check82 : integerHullCheck (integerOverlayPlanes ![6,6,9,6]) fractionRow82 = true := by decide
theorem vertices_fit82 (p : Point) (hp : p ∈ rationalHull rationalRow82) :
    ∀ g, ClosedCell ((![6,6,9,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow82_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check82 p hp
theorem fractionRow83_correct : fractionRow83.map FractionPoint.rational = rationalRow83 := by
  simp only [fractionRow83, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check83 : integerHullCheck (integerOverlayPlanes ![6,6,9,9]) fractionRow83 = true := by decide
theorem vertices_fit83 (p : Point) (hp : p ∈ rationalHull rationalRow83) :
    ∀ g, ClosedCell ((![6,6,9,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow83_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check83 p hp
theorem fractionRow84_correct : fractionRow84.map FractionPoint.rational = rationalRow84 := by
  simp only [fractionRow84, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check84 : integerHullCheck (integerOverlayPlanes ![6,9,6,6]) fractionRow84 = true := by decide
theorem vertices_fit84 (p : Point) (hp : p ∈ rationalHull rationalRow84) :
    ∀ g, ClosedCell ((![6,9,6,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow84_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check84 p hp
theorem fractionRow85_correct : fractionRow85.map FractionPoint.rational = rationalRow85 := by
  simp only [fractionRow85, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check85 : integerHullCheck (integerOverlayPlanes ![6,9,6,9]) fractionRow85 = true := by decide
theorem vertices_fit85 (p : Point) (hp : p ∈ rationalHull rationalRow85) :
    ∀ g, ClosedCell ((![6,9,6,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow85_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check85 p hp
theorem fractionRow86_correct : fractionRow86.map FractionPoint.rational = rationalRow86 := by
  simp only [fractionRow86, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check86 : integerHullCheck (integerOverlayPlanes ![6,9,9,6]) fractionRow86 = true := by decide
theorem vertices_fit86 (p : Point) (hp : p ∈ rationalHull rationalRow86) :
    ∀ g, ClosedCell ((![6,9,9,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow86_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check86 p hp
theorem fractionRow87_correct : fractionRow87.map FractionPoint.rational = rationalRow87 := by
  simp only [fractionRow87, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check87 : integerHullCheck (integerOverlayPlanes ![6,9,9,9]) fractionRow87 = true := by decide
theorem vertices_fit87 (p : Point) (hp : p ∈ rationalHull rationalRow87) :
    ∀ g, ClosedCell ((![6,9,9,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow87_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check87 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit80
