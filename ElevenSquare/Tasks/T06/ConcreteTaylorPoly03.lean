import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly012 :
    |polyEval (![(-181 / 400), (-691 / 400), (1529 / 400), (691 / 400), (-359 / 80), (-701 / 400), (55 / 16), (-87 / 80)]) u| ≤ ((57294549 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-181 / 400), (-691 / 400), (1529 / 400), (691 / 400), (-359 / 80), (-701 / 400), (55 / 16), (-87 / 80)]) ((57294549 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly013 :
    |polyEval (![(-9 / 20), (-23 / 40), (141 / 20), (-167 / 40), (-31 / 4), (-33 / 40), (25 / 4), (-21 / 8)]) u| ≤ ((5287349 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-9 / 20), (-23 / 40), (141 / 20), (-167 / 40), (-31 / 4), (-33 / 40), (25 / 4), (-21 / 8)]) ((5287349 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly014 :
    |polyEval (![(-11 / 25), (-343 / 200), (74 / 25), (-557 / 200), (-24 / 5), (227 / 200), (5 / 2), (-51 / 40)]) u| ≤ ((88118359 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-11 / 25), (-343 / 200), (74 / 25), (-557 / 200), (-24 / 5), (227 / 200), (5 / 2), (-51 / 40)]) ((88118359 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly015 :
    |polyEval (![(-17 / 40), (-27 / 40), (203 / 40), (-153 / 40), (-51 / 8), (-37 / 40), (45 / 8), (-19 / 8)]) u| ≤ ((28887401 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-17 / 40), (-27 / 40), (203 / 40), (-153 / 40), (-51 / 8), (-37 / 40), (45 / 8), (-19 / 8)]) ((28887401 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
