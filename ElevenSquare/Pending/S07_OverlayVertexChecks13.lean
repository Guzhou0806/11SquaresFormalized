import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow104_correct : fractionRow104.map FractionPoint.rational = rationalRow104 := by
  simp only [fractionRow104, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check104 : integerHullCheck (integerOverlayPlanes ![7,4,14,14]) fractionRow104 = true := by decide
theorem vertices_fit104 (p : Point) (hp : p ∈ rationalHull rationalRow104) :
    ∀ g, ClosedCell ((![7,4,14,14] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow104_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check104 p hp
theorem fractionRow105_correct : fractionRow105.map FractionPoint.rational = rationalRow105 := by
  simp only [fractionRow105, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check105 : integerHullCheck (integerOverlayPlanes ![7,4,15,13]) fractionRow105 = true := by decide
theorem vertices_fit105 (p : Point) (hp : p ∈ rationalHull rationalRow105) :
    ∀ g, ClosedCell ((![7,4,15,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow105_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check105 p hp
theorem fractionRow106_correct : fractionRow106.map FractionPoint.rational = rationalRow106 := by
  simp only [fractionRow106, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check106 : integerHullCheck (integerOverlayPlanes ![7,5,10,8]) fractionRow106 = true := by decide
theorem vertices_fit106 (p : Point) (hp : p ∈ rationalHull rationalRow106) :
    ∀ g, ClosedCell ((![7,5,10,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow106_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check106 p hp
theorem fractionRow107_correct : fractionRow107.map FractionPoint.rational = rationalRow107 := by
  simp only [fractionRow107, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check107 : integerHullCheck (integerOverlayPlanes ![7,5,10,12]) fractionRow107 = true := by decide
theorem vertices_fit107 (p : Point) (hp : p ∈ rationalHull rationalRow107) :
    ∀ g, ClosedCell ((![7,5,10,12] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow107_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check107 p hp
theorem fractionRow108_correct : fractionRow108.map FractionPoint.rational = rationalRow108 := by
  simp only [fractionRow108, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check108 : integerHullCheck (integerOverlayPlanes ![7,5,10,13]) fractionRow108 = true := by decide
theorem vertices_fit108 (p : Point) (hp : p ∈ rationalHull rationalRow108) :
    ∀ g, ClosedCell ((![7,5,10,13] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow108_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check108 p hp
theorem fractionRow109_correct : fractionRow109.map FractionPoint.rational = rationalRow109 := by
  simp only [fractionRow109, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check109 : integerHullCheck (integerOverlayPlanes ![7,5,15,8]) fractionRow109 = true := by decide
theorem vertices_fit109 (p : Point) (hp : p ∈ rationalHull rationalRow109) :
    ∀ g, ClosedCell ((![7,5,15,8] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow109_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check109 p hp
theorem fractionRow110_correct : fractionRow110.map FractionPoint.rational = rationalRow110 := by
  simp only [fractionRow110, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check110 : integerHullCheck (integerOverlayPlanes ![8,10,0,7]) fractionRow110 = true := by decide
theorem vertices_fit110 (p : Point) (hp : p ∈ rationalHull rationalRow110) :
    ∀ g, ClosedCell ((![8,10,0,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow110_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check110 p hp
theorem fractionRow111_correct : fractionRow111.map FractionPoint.rational = rationalRow111 := by
  simp only [fractionRow111, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check111 : integerHullCheck (integerOverlayPlanes ![8,10,5,2]) fractionRow111 = true := by decide
theorem vertices_fit111 (p : Point) (hp : p ∈ rationalHull rationalRow111) :
    ∀ g, ClosedCell ((![8,10,5,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow111_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check111 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit104
