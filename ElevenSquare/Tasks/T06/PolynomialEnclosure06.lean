import ElevenSquare.Tasks.T06.PolynomialData

namespace ElevenSquare.Pending.T06
noncomputable section
set_option maxRecDepth 10000

theorem gradient_error_06 :
    |polyEval (gradientCoefficients 6) u - gradientRounded 6| ≤ (1/1000000000000 : ℝ) := by
  have he : (((1/1000000000000 : ℚ) : ℝ)) = 1/1000000000000 := by norm_num
  rw [← he]
  apply poly_rounding_error _ (365769307604677293388545018143 / 1000000000000000000000000000000) (365769307604677293388545018144 / 1000000000000000000000000000000)
  · norm_num
  · simpa [rootLo] using u_bounds.1.le
  · simpa [rootHi] using u_bounds.2.le
  · change (-763999473636 / 1000000000000) - (1 / 1000000000000) ≤ polyLower ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] (365769307604677293388545018143 / 1000000000000000000000000000000) (365769307604677293388545018144 / 1000000000000000000000000000000)
    norm_num [polyLower, Fin.sum_univ_succ]
  · change polyUpper ![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)] (365769307604677293388545018143 / 1000000000000000000000000000000) (365769307604677293388545018144 / 1000000000000000000000000000000) ≤ (-763999473636 / 1000000000000) + (1 / 1000000000000)
    norm_num [polyUpper, Fin.sum_univ_succ]

end
end ElevenSquare.Pending.T06
