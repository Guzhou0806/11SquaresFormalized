import ElevenSquare.Tasks.T06.Gradients
import ElevenSquare.Tasks.T06.GradientsPolynomial

namespace ElevenSquare.Pending.T06
noncomputable section

theorem polyEval_zero (x : ℝ) : polyEval ![0, 0, 0, 0, 0, 0, 0, 0] x = 0 := by
  rw [polyEval_vec]
  simp

theorem wallGradientFormula_zero (q₀ : Owner → UnitSquare) (i : Owner)
    (v w : Fin 4) (j : Fin 33)
    (hx : coordinate i 0 ≠ j) (hy : coordinate i 1 ≠ j)
    (hθ : coordinate i 2 ≠ j) : wallGradientFormula q₀ i v w j = 0 := by
  fin_cases w <;> simp [wallGradientFormula, cornerVelocity, centerVelocity,
    axisVelocity, coordinateDelta, hx, hy, hθ, perp]

theorem pairGradientFormula_zero (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (j : Fin 33)
    (hox : coordinate f.owner 0 ≠ j) (hoy : coordinate f.owner 1 ≠ j)
    (hoθ : coordinate f.owner 2 ≠ j)
    (hpx : coordinate f.other 0 ≠ j) (hpy : coordinate f.other 1 ≠ j)
    (hpθ : coordinate f.other 2 ≠ j) : pairGradientFormula q₀ f v j = 0 := by
  simp [pairGradientFormula, cornerVelocity, centerVelocity, axisVelocity,
    normalVelocity, coordinateDelta, hox, hoy, hoθ, hpx, hpy, hpθ, perp, dot]

end
end ElevenSquare.Pending.T06
