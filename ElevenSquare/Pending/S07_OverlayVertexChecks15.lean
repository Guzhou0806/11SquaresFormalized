import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow120_correct : fractionRow120.map FractionPoint.rational = rationalRow120 := by
  simp only [fractionRow120, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check120 : integerHullCheck (integerOverlayPlanes ![8,15,0,3]) fractionRow120 = true := by decide
theorem vertices_fit120 (p : Point) (hp : p ∈ rationalHull rationalRow120) :
    ∀ g, ClosedCell ((![8,15,0,3] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow120_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check120 p hp
theorem fractionRow121_correct : fractionRow121.map FractionPoint.rational = rationalRow121 := by
  simp only [fractionRow121, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check121 : integerHullCheck (integerOverlayPlanes ![8,15,0,7]) fractionRow121 = true := by decide
theorem vertices_fit121 (p : Point) (hp : p ∈ rationalHull rationalRow121) :
    ∀ g, ClosedCell ((![8,15,0,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow121_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check121 p hp
theorem fractionRow122_correct : fractionRow122.map FractionPoint.rational = rationalRow122 := by
  simp only [fractionRow122, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check122 : integerHullCheck (integerOverlayPlanes ![8,15,1,2]) fractionRow122 = true := by decide
theorem vertices_fit122 (p : Point) (hp : p ∈ rationalHull rationalRow122) :
    ∀ g, ClosedCell ((![8,15,1,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow122_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check122 p hp
theorem fractionRow123_correct : fractionRow123.map FractionPoint.rational = rationalRow123 := by
  simp only [fractionRow123, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check123 : integerHullCheck (integerOverlayPlanes ![8,15,1,3]) fractionRow123 = true := by decide
theorem vertices_fit123 (p : Point) (hp : p ∈ rationalHull rationalRow123) :
    ∀ g, ClosedCell ((![8,15,1,3] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow123_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check123 p hp
theorem fractionRow124_correct : fractionRow124.map FractionPoint.rational = rationalRow124 := by
  simp only [fractionRow124, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check124 : integerHullCheck (integerOverlayPlanes ![8,15,5,2]) fractionRow124 = true := by decide
theorem vertices_fit124 (p : Point) (hp : p ∈ rationalHull rationalRow124) :
    ∀ g, ClosedCell ((![8,15,5,2] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow124_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check124 p hp
theorem fractionRow125_correct : fractionRow125.map FractionPoint.rational = rationalRow125 := by
  simp only [fractionRow125, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check125 : integerHullCheck (integerOverlayPlanes ![8,15,5,3]) fractionRow125 = true := by decide
theorem vertices_fit125 (p : Point) (hp : p ∈ rationalHull rationalRow125) :
    ∀ g, ClosedCell ((![8,15,5,3] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow125_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check125 p hp
theorem fractionRow126_correct : fractionRow126.map FractionPoint.rational = rationalRow126 := by
  simp only [fractionRow126, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check126 : integerHullCheck (integerOverlayPlanes ![8,15,5,7]) fractionRow126 = true := by decide
theorem vertices_fit126 (p : Point) (hp : p ∈ rationalHull rationalRow126) :
    ∀ g, ClosedCell ((![8,15,5,7] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow126_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check126 p hp
theorem fractionRow127_correct : fractionRow127.map FractionPoint.rational = rationalRow127 := by
  simp only [fractionRow127, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check127 : integerHullCheck (integerOverlayPlanes ![9,6,2,5]) fractionRow127 = true := by decide
theorem vertices_fit127 (p : Point) (hp : p ∈ rationalHull rationalRow127) :
    ∀ g, ClosedCell ((![9,6,2,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow127_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check127 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit120
