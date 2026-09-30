import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly032 :
    |polyEval (![0, 0, 0, 0, 0, 0, 0, 0]) u| ≤ (0 : ℝ) := by
  have h := concrete_poly_abs_bound (![0, 0, 0, 0, 0, 0, 0, 0]) (0)
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly033 :
    |polyEval (![(1 / 40), (21 / 40), (-49 / 40), (159 / 40), (43 / 8), (-9 / 40), (-35 / 8), (17 / 8)]) u| ≤ ((33377597 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(1 / 40), (21 / 40), (-49 / 40), (159 / 40), (43 / 8), (-9 / 40), (-35 / 8), (17 / 8)]) ((33377597 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly034 :
    |polyEval (![(7 / 200), (-137 / 50), (587 / 200), (137 / 50), (-147 / 40), (-107 / 50), (25 / 8), (-9 / 10)]) u| ≤ ((51355419 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(7 / 200), (-137 / 50), (587 / 200), (137 / 50), (-147 / 40), (-107 / 50), (25 / 8), (-9 / 10)]) ((51355419 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly035 :
    |polyEval (![(3 / 80), (-127 / 80), (493 / 80), (-253 / 80), (-111 / 16), (-97 / 80), (95 / 16), (-39 / 16)]) u| ≤ ((651783 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(3 / 80), (-127 / 80), (493 / 80), (-253 / 80), (-111 / 16), (-97 / 80), (95 / 16), (-39 / 16)]) ((651783 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
