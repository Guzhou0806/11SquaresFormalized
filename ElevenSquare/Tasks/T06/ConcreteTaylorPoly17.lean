import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly068 :
    |polyEval (![(89 / 100), (183 / 200), (-119 / 25), (567 / 200), (121 / 20), (213 / 200), -5, (81 / 40)]) u| ≤ ((2079113 / 2500000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(89 / 100), (183 / 200), (-119 / 25), (567 / 200), (121 / 20), (213 / 200), -5, (81 / 40)]) ((2079113 / 2500000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly069 :
    |polyEval (![(371 / 400), (281 / 400), (-1539 / 400), (1519 / 400), (449 / 80), (-609 / 400), (-45 / 16), (117 / 80)]) u| ≤ ((94057489 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(371 / 400), (281 / 400), (-1539 / 400), (1519 / 400), (449 / 80), (-609 / 400), (-45 / 16), (117 / 80)]) ((94057489 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly070 :
    |polyEval (![(47 / 50), (143 / 200), (-471 / 100), (-143 / 200), (53 / 10), (273 / 200), (-15 / 4), (51 / 40)]) u| ≤ ((790421 / 1250000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(47 / 50), (143 / 200), (-471 / 100), (-143 / 200), (53 / 10), (273 / 200), (-15 / 4), (51 / 40)]) ((790421 / 1250000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly071 :
    |polyEval (![(39 / 40), (-81 / 40), (-71 / 40), (81 / 40), (13 / 8), (-31 / 40), (-5 / 8), (3 / 8)]) u| ≤ ((11878261 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(39 / 40), (-81 / 40), (-71 / 40), (81 / 40), (13 / 8), (-31 / 40), (-5 / 8), (3 / 8)]) ((11878261 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
