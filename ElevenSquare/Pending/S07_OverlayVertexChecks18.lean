import ElevenSquare.Pending.S07_OverlayFractions
import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem fractionRow144_correct : fractionRow144.map FractionPoint.rational = rationalRow144 := by
  simp only [fractionRow144, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check144 : integerHullCheck (integerOverlayPlanes ![9,11,5,5]) fractionRow144 = true := by decide
theorem vertices_fit144 (p : Point) (hp : p ∈ rationalHull rationalRow144) :
    ∀ g, ClosedCell ((![9,11,5,5] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow144_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check144 p hp
theorem fractionRow145_correct : fractionRow145.map FractionPoint.rational = rationalRow145 := by
  simp only [fractionRow145, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check145 : integerHullCheck (integerOverlayPlanes ![10,8,8,10]) fractionRow145 = true := by decide
theorem vertices_fit145 (p : Point) (hp : p ∈ rationalHull rationalRow145) :
    ∀ g, ClosedCell ((![10,8,8,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow145_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check145 p hp
theorem fractionRow146_correct : fractionRow146.map FractionPoint.rational = rationalRow146 := by
  simp only [fractionRow146, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check146 : integerHullCheck (integerOverlayPlanes ![10,8,8,15]) fractionRow146 = true := by decide
theorem vertices_fit146 (p : Point) (hp : p ∈ rationalHull rationalRow146) :
    ∀ g, ClosedCell ((![10,8,8,15] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow146_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check146 p hp
theorem fractionRow147_correct : fractionRow147.map FractionPoint.rational = rationalRow147 := by
  simp only [fractionRow147, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check147 : integerHullCheck (integerOverlayPlanes ![10,8,12,10]) fractionRow147 = true := by decide
theorem vertices_fit147 (p : Point) (hp : p ∈ rationalHull rationalRow147) :
    ∀ g, ClosedCell ((![10,8,12,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow147_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check147 p hp
theorem fractionRow148_correct : fractionRow148.map FractionPoint.rational = rationalRow148 := by
  simp only [fractionRow148, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check148 : integerHullCheck (integerOverlayPlanes ![10,8,13,10]) fractionRow148 = true := by decide
theorem vertices_fit148 (p : Point) (hp : p ∈ rationalHull rationalRow148) :
    ∀ g, ClosedCell ((![10,8,13,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow148_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check148 p hp
theorem fractionRow149_correct : fractionRow149.map FractionPoint.rational = rationalRow149 := by
  simp only [fractionRow149, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check149 : integerHullCheck (integerOverlayPlanes ![10,9,9,6]) fractionRow149 = true := by decide
theorem vertices_fit149 (p : Point) (hp : p ∈ rationalHull rationalRow149) :
    ∀ g, ClosedCell ((![10,9,9,6] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow149_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check149 p hp
theorem fractionRow150_correct : fractionRow150.map FractionPoint.rational = rationalRow150 := by
  simp only [fractionRow150, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check150 : integerHullCheck (integerOverlayPlanes ![10,9,9,10]) fractionRow150 = true := by decide
theorem vertices_fit150 (p : Point) (hp : p ∈ rationalHull rationalRow150) :
    ∀ g, ClosedCell ((![10,9,9,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow150_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check150 p hp
theorem fractionRow151_correct : fractionRow151.map FractionPoint.rational = rationalRow151 := by
  simp only [fractionRow151, FractionPoint.rational, List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_zero, Int.cast_one, div_one, zero_div] <;> rfl
set_option maxRecDepth 8192 in
theorem vertices_check151 : integerHullCheck (integerOverlayPlanes ![10,9,13,10]) fractionRow151 = true := by decide
theorem vertices_fit151 (p : Point) (hp : p ∈ rationalHull rationalRow151) :
    ∀ g, ClosedCell ((![10,9,13,10] : Fin 4 → Fin 16) g) (view g p) := by
  rw [← fractionRow151_correct] at hp
  exact integerHullCheck_overlay _ _ vertices_check151 p hp
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_fit144
