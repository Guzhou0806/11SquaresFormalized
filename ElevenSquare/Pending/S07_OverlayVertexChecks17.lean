import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow136_correct : fractionRow136.map FractionPoint.rational = rationalRow136 := by
  simp only [fractionRow136, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check136 : integerHullCheck (integerOverlayPlanes ![9,9,6,6]) fractionRow136 = true := by decide
theorem vertices_fit136 (p : Point) (hp : p ∈ rationalHull rationalRow136) :
    ∀ g, ClosedCell ((![9,9,6,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow136_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check136 p hp
theorem fractionRow137_correct : fractionRow137.map FractionPoint.rational = rationalRow137 := by
  simp only [fractionRow137, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check137 : integerHullCheck (integerOverlayPlanes ![9,9,6,9]) fractionRow137 = true := by decide
theorem vertices_fit137 (p : Point) (hp : p ∈ rationalHull rationalRow137) :
    ∀ g, ClosedCell ((![9,9,6,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow137_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check137 p hp
theorem fractionRow138_correct : fractionRow138.map FractionPoint.rational = rationalRow138 := by
  simp only [fractionRow138, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check138 : integerHullCheck (integerOverlayPlanes ![9,9,9,6]) fractionRow138 = true := by decide
theorem vertices_fit138 (p : Point) (hp : p ∈ rationalHull rationalRow138) :
    ∀ g, ClosedCell ((![9,9,9,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow138_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check138 p hp
theorem fractionRow139_correct : fractionRow139.map FractionPoint.rational = rationalRow139 := by
  simp only [fractionRow139, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check139 : integerHullCheck (integerOverlayPlanes ![9,9,9,9]) fractionRow139 = true := by decide
theorem vertices_fit139 (p : Point) (hp : p ∈ rationalHull rationalRow139) :
    ∀ g, ClosedCell ((![9,9,9,9] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow139_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check139 p hp
theorem fractionRow140_correct : fractionRow140.map FractionPoint.rational = rationalRow140 := by
  simp only [fractionRow140, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check140 : integerHullCheck (integerOverlayPlanes ![9,10,5,2]) fractionRow140 = true := by decide
theorem vertices_fit140 (p : Point) (hp : p ∈ rationalHull rationalRow140) :
    ∀ g, ClosedCell ((![9,10,5,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow140_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check140 p hp
theorem fractionRow141_correct : fractionRow141.map FractionPoint.rational = rationalRow141 := by
  simp only [fractionRow141, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check141 : integerHullCheck (integerOverlayPlanes ![9,10,5,6]) fractionRow141 = true := by decide
theorem vertices_fit141 (p : Point) (hp : p ∈ rationalHull rationalRow141) :
    ∀ g, ClosedCell ((![9,10,5,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow141_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check141 p hp
theorem fractionRow142_correct : fractionRow142.map FractionPoint.rational = rationalRow142 := by
  simp only [fractionRow142, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check142 : integerHullCheck (integerOverlayPlanes ![9,10,9,6]) fractionRow142 = true := by decide
theorem vertices_fit142 (p : Point) (hp : p ∈ rationalHull rationalRow142) :
    ∀ g, ClosedCell ((![9,10,9,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow142_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check142 p hp
theorem fractionRow143_correct : fractionRow143.map FractionPoint.rational = rationalRow143 := by
  simp only [fractionRow143, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check143 : integerHullCheck (integerOverlayPlanes ![9,11,5,2]) fractionRow143 = true := by decide
theorem vertices_fit143 (p : Point) (hp : p ∈ rationalHull rationalRow143) :
    ∀ g, ClosedCell ((![9,11,5,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow143_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check143 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit136
