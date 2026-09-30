import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow176_correct : fractionRow176.map FractionPoint.rational = rationalRow176 := by
  simp only [fractionRow176, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check176 : integerHullCheck (integerOverlayPlanes ![11,8,13,15]) fractionRow176 = true := by decide
theorem vertices_fit176 (p : Point) (hp : p ∈ rationalHull rationalRow176) :
    ∀ g, ClosedCell ((![11,8,13,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow176_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check176 p hp
theorem fractionRow177_correct : fractionRow177.map FractionPoint.rational = rationalRow177 := by
  simp only [fractionRow177, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check177 : integerHullCheck (integerOverlayPlanes ![11,8,14,14]) fractionRow177 = true := by decide
theorem vertices_fit177 (p : Point) (hp : p ∈ rationalHull rationalRow177) :
    ∀ g, ClosedCell ((![11,8,14,14] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow177_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check177 p hp
theorem fractionRow178_correct : fractionRow178.map FractionPoint.rational = rationalRow178 := by
  simp only [fractionRow178, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check178 : integerHullCheck (integerOverlayPlanes ![11,9,10,10]) fractionRow178 = true := by decide
theorem vertices_fit178 (p : Point) (hp : p ∈ rationalHull rationalRow178) :
    ∀ g, ClosedCell ((![11,9,10,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow178_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check178 p hp
theorem fractionRow179_correct : fractionRow179.map FractionPoint.rational = rationalRow179 := by
  simp only [fractionRow179, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check179 : integerHullCheck (integerOverlayPlanes ![11,9,13,10]) fractionRow179 = true := by decide
theorem vertices_fit179 (p : Point) (hp : p ∈ rationalHull rationalRow179) :
    ∀ g, ClosedCell ((![11,9,13,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow179_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check179 p hp
theorem fractionRow180_correct : fractionRow180.map FractionPoint.rational = rationalRow180 := by
  simp only [fractionRow180, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check180 : integerHullCheck (integerOverlayPlanes ![12,10,0,7]) fractionRow180 = true := by decide
theorem vertices_fit180 (p : Point) (hp : p ∈ rationalHull rationalRow180) :
    ∀ g, ClosedCell ((![12,10,0,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow180_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check180 p hp
theorem fractionRow181_correct : fractionRow181.map FractionPoint.rational = rationalRow181 := by
  simp only [fractionRow181, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check181 : integerHullCheck (integerOverlayPlanes ![12,10,5,7]) fractionRow181 = true := by decide
theorem vertices_fit181 (p : Point) (hp : p ∈ rationalHull rationalRow181) :
    ∀ g, ClosedCell ((![12,10,5,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow181_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check181 p hp
theorem fractionRow182_correct : fractionRow182.map FractionPoint.rational = rationalRow182 := by
  simp only [fractionRow182, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check182 : integerHullCheck (integerOverlayPlanes ![12,14,0,7]) fractionRow182 = true := by decide
theorem vertices_fit182 (p : Point) (hp : p ∈ rationalHull rationalRow182) :
    ∀ g, ClosedCell ((![12,14,0,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow182_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check182 p hp
theorem fractionRow183_correct : fractionRow183.map FractionPoint.rational = rationalRow183 := by
  simp only [fractionRow183, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check183 : integerHullCheck (integerOverlayPlanes ![12,14,4,7]) fractionRow183 = true := by decide
theorem vertices_fit183 (p : Point) (hp : p ∈ rationalHull rationalRow183) :
    ∀ g, ClosedCell ((![12,14,4,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow183_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check183 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit176
