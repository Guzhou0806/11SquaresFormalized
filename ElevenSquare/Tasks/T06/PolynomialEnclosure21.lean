import ElevenSquare.Tasks.T06.PolynomialData

namespace ElevenSquare.Pending.T06
noncomputable section
set_option maxRecDepth 10000

theorem gradient_error_21 :
    |polyEval (gradientCoefficients 21) u - gradientRounded 21| ≤ (1/1000000000000 : ℝ) := by
  have he : (((1/1000000000000 : ℚ) : ℝ)) = 1/1000000000000 := by norm_num
  rw [← he]
  apply poly_rounding_error _ (365769307604677293388545018143 / 1000000000000000000000000000000) (365769307604677293388545018144 / 1000000000000000000000000000000)
  · norm_num
  · simpa [rootLo] using u_bounds.1.le
  · simpa [rootHi] using u_bounds.2.le
  · change (-166224039637 / 1000000000000) - (1 / 1000000000000) ≤ polyLower ![(-19 / 40), (21 / 40), (-49 / 40), (159 / 40), (43 / 8), (-9 / 40), (-35 / 8), (17 / 8)] (365769307604677293388545018143 / 1000000000000000000000000000000) (365769307604677293388545018144 / 1000000000000000000000000000000)
    norm_num [polyLower, Fin.sum_univ_succ]
  · change polyUpper ![(-19 / 40), (21 / 40), (-49 / 40), (159 / 40), (43 / 8), (-9 / 40), (-35 / 8), (17 / 8)] (365769307604677293388545018143 / 1000000000000000000000000000000) (365769307604677293388545018144 / 1000000000000000000000000000000) ≤ (-166224039637 / 1000000000000) + (1 / 1000000000000)
    norm_num [polyUpper, Fin.sum_univ_succ]

end
end ElevenSquare.Pending.T06
