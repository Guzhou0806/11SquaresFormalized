import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow184_correct : fractionRow184.map FractionPoint.rational = rationalRow184 := by
  simp only [fractionRow184, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check184 : integerHullCheck (integerOverlayPlanes ![12,15,0,3]) fractionRow184 = true := by decide
theorem vertices_fit184 (p : Point) (hp : p ∈ rationalHull rationalRow184) :
    ∀ g, ClosedCell ((![12,15,0,3] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow184_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check184 p hp
theorem fractionRow185_correct : fractionRow185.map FractionPoint.rational = rationalRow185 := by
  simp only [fractionRow185, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check185 : integerHullCheck (integerOverlayPlanes ![12,15,0,7]) fractionRow185 = true := by decide
theorem vertices_fit185 (p : Point) (hp : p ∈ rationalHull rationalRow185) :
    ∀ g, ClosedCell ((![12,15,0,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow185_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check185 p hp
theorem fractionRow186_correct : fractionRow186.map FractionPoint.rational = rationalRow186 := by
  simp only [fractionRow186, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check186 : integerHullCheck (integerOverlayPlanes ![13,10,0,7]) fractionRow186 = true := by decide
theorem vertices_fit186 (p : Point) (hp : p ∈ rationalHull rationalRow186) :
    ∀ g, ClosedCell ((![13,10,0,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow186_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check186 p hp
theorem fractionRow187_correct : fractionRow187.map FractionPoint.rational = rationalRow187 := by
  simp only [fractionRow187, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check187 : integerHullCheck (integerOverlayPlanes ![13,10,4,6]) fractionRow187 = true := by decide
theorem vertices_fit187 (p : Point) (hp : p ∈ rationalHull rationalRow187) :
    ∀ g, ClosedCell ((![13,10,4,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow187_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check187 p hp
theorem fractionRow188_correct : fractionRow188.map FractionPoint.rational = rationalRow188 := by
  simp only [fractionRow188, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check188 : integerHullCheck (integerOverlayPlanes ![13,10,4,7]) fractionRow188 = true := by decide
theorem vertices_fit188 (p : Point) (hp : p ∈ rationalHull rationalRow188) :
    ∀ g, ClosedCell ((![13,10,4,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow188_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check188 p hp
theorem fractionRow189_correct : fractionRow189.map FractionPoint.rational = rationalRow189 := by
  simp only [fractionRow189, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check189 : integerHullCheck (integerOverlayPlanes ![13,10,4,11]) fractionRow189 = true := by decide
theorem vertices_fit189 (p : Point) (hp : p ∈ rationalHull rationalRow189) :
    ∀ g, ClosedCell ((![13,10,4,11] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow189_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check189 p hp
theorem fractionRow190_correct : fractionRow190.map FractionPoint.rational = rationalRow190 := by
  simp only [fractionRow190, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check190 : integerHullCheck (integerOverlayPlanes ![13,10,5,2]) fractionRow190 = true := by decide
theorem vertices_fit190 (p : Point) (hp : p ∈ rationalHull rationalRow190) :
    ∀ g, ClosedCell ((![13,10,5,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow190_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check190 p hp
theorem fractionRow191_correct : fractionRow191.map FractionPoint.rational = rationalRow191 := by
  simp only [fractionRow191, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check191 : integerHullCheck (integerOverlayPlanes ![13,10,5,6]) fractionRow191 = true := by decide
theorem vertices_fit191 (p : Point) (hp : p ∈ rationalHull rationalRow191) :
    ∀ g, ClosedCell ((![13,10,5,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow191_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check191 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit184
