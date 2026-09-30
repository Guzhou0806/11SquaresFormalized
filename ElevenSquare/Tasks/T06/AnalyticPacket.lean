import ElevenSquare.Tasks.T06.AnalyticPairs
import ElevenSquare.Pending.S08_Packet

namespace ElevenSquare.Pending.T06
noncomputable section

def gapRectangleCurvature (q₀ : Owner → UnitSquare) (r : Fin 33 → ℝ) : Gap → ℝ
  | .pair f v => featureRectangleCurvature q₀ r f v
  | .wall i v _ => wallRectangleCurvature q₀ r i v

theorem gap_rectangle_taylor (S : ℝ) (q₀ : Owner → UnitSquare)
    (r : Fin 33 → ℝ) (g : Gap) (h : Displacement) (hr : InRectangle r h)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    |gapValue S q₀ g (τ • h)-gapValue S q₀ g 0-
      τ*LinearForm (gapGradient S q₀ g) h| ≤ τ^2*gapRectangleCurvature q₀ r g/2 := by
  cases g with
  | pair f v => exact feature_gap_taylor_on_rectangle S q₀ r f v h hr τ hτ
  | wall i v w => exact wall_gap_taylor_on_rectangle S q₀ r h hr i v w τ hτ

theorem rowsTaylorBound_of_curvatures (S : ℝ) (q₀ : Owner → UnitSquare)
    (p : LocalPacket) (htied : RowsTied S q₀ p)
    (hK : ∀ b i g, g ∈ p.aliases b i →
      gapRectangleCurvature q₀ p.radii g ≤ (p.curvature b i : ℝ)) :
    RowsTaylorBound S q₀ p := by
  intro b i g hg h hr τ hτ
  have hb := gap_rectangle_taylor S q₀ p.radii g h hr τ hτ
  rw [((htied b i).2 g hg).2] at hb
  exact hb.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hK b i g hg) (sq_nonneg τ)) (by norm_num))

theorem gap_negative_on_rectangle (S : ℝ) (q₀ : Owner → UnitSquare)
    (r : Fin 33 → ℝ) (g : Gap)
    (hmargin : gapValue S q₀ g 0 + (∑ j, |gapGradient S q₀ g j| * r j) +
      gapRectangleCurvature q₀ r g/2 < 0) :
    ∀ h, InRectangle r h → gapValue S q₀ g h < 0 := by
  apply negative_gap_on_rectangle (gapValue S q₀ g) (gapGradient S q₀ g) r
    (gapRectangleCurvature q₀ r g) _ hmargin
  intro h hr
  simpa using gap_rectangle_taylor S q₀ r g h hr 1 (by norm_num)

end
end ElevenSquare.Pending.T06
