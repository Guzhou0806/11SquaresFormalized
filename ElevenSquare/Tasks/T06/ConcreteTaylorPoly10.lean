import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly040 :
    |polyEval (![(1 / 16), (13 / 16), (-49 / 16), (-5 / 16), (31 / 16), (3 / 16), (-15 / 16), (5 / 16)]) u| ≤ ((784809 / 25000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(1 / 16), (13 / 16), (-49 / 16), (-5 / 16), (31 / 16), (3 / 16), (-15 / 16), (5 / 16)]) ((784809 / 25000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly041 :
    |polyEval (![(1 / 16), (23 / 16), (-37 / 16), (53 / 16), (95 / 16), (1 / 16), (-75 / 16), (35 / 16)]) u| ≤ ((26919207 / 50000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(1 / 16), (23 / 16), (-37 / 16), (53 / 16), (95 / 16), (1 / 16), (-75 / 16), (35 / 16)]) ((26919207 / 50000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly042 :
    |polyEval (![(17 / 200), (-147 / 50), (597 / 200), (-81 / 100), (-177 / 40), (-46 / 25), (35 / 8), (-33 / 20)]) u| ≤ ((3564313 / 5000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(17 / 200), (-147 / 50), (597 / 200), (-81 / 100), (-177 / 40), (-46 / 25), (35 / 8), (-33 / 20)]) ((3564313 / 5000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly043 :
    |polyEval (![(1 / 10), (-31 / 40), (31 / 10), (-139 / 40), -5, (-41 / 40), 5, (-17 / 8)]) u| ≤ ((1243727 / 50000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(1 / 10), (-31 / 40), (31 / 10), (-139 / 40), -5, (-41 / 40), 5, (-17 / 8)]) ((1243727 / 50000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
