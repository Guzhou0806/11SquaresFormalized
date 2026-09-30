import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly024 :
    |polyEval (![(-1 / 10), (31 / 40), (-31 / 10), (139 / 40), 5, (41 / 40), -5, (17 / 8)]) u| ≤ ((1243727 / 50000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-1 / 10), (31 / 40), (-31 / 10), (139 / 40), 5, (41 / 40), -5, (17 / 8)]) ((1243727 / 50000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly025 :
    |polyEval (![(-1 / 16), (-13 / 16), (49 / 16), (5 / 16), (-31 / 16), (-3 / 16), (15 / 16), (-5 / 16)]) u| ≤ ((784809 / 25000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-1 / 16), (-13 / 16), (49 / 16), (5 / 16), (-31 / 16), (-3 / 16), (15 / 16), (-5 / 16)]) ((784809 / 25000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly026 :
    |polyEval (![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)]) u| ≤ ((64521687 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-1 / 20), (-77 / 40), (1 / 5), (67 / 40), (1 / 4), (-27 / 40), 0, (1 / 8)]) ((64521687 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly027 :
    |polyEval (![(-19 / 400), (-309 / 400), (371 / 400), (-1691 / 400), (-241 / 80), (101 / 400), (45 / 16), (-113 / 80)]) u| ≤ ((45961283 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-19 / 400), (-309 / 400), (371 / 400), (-1691 / 400), (-241 / 80), (101 / 400), (45 / 16), (-113 / 80)]) ((45961283 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
