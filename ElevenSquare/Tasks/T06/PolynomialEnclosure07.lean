import ElevenSquare.Tasks.T06.PolynomialData

namespace ElevenSquare.Pending.T06
noncomputable section
set_option maxRecDepth 10000

theorem gradient_error_07 :
    |polyEval (gradientCoefficients 7) u - gradientRounded 7| ≤ (1/1000000000000 : ℝ) := by
  have he : (((1/1000000000000 : ℚ) : ℝ)) = 1/1000000000000 := by norm_num
  rw [← he]
  apply poly_rounding_error _ (365769307604677293388545018143 / 1000000000000000000000000000000) (365769307604677293388545018144 / 1000000000000000000000000000000)
  · norm_num
  · simpa [rootLo] using u_bounds.1.le
  · simpa [rootHi] using u_bounds.2.le
  · change (-645216866087 / 1000000000000) - (1 / 1000000000000) ≤ polyLower ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] (365769307604677293388545018143 / 1000000000000000000000000000000) (365769307604677293388545018144 / 1000000000000000000000000000000)
    norm_num [polyLower, Fin.sum_univ_succ]
  · change polyUpper ![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)] (365769307604677293388545018143 / 1000000000000000000000000000000) (365769307604677293388545018144 / 1000000000000000000000000000000) ≤ (-645216866087 / 1000000000000) + (1 / 1000000000000)
    norm_num [polyUpper, Fin.sum_univ_succ]

end
end ElevenSquare.Pending.T06
