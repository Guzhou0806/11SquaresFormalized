import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly004 :
    |polyEval (![(-39 / 40), (81 / 40), (71 / 40), (-81 / 40), (-13 / 8), (31 / 40), (5 / 8), (-3 / 8)]) u| ≤ ((11878261 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-39 / 40), (81 / 40), (71 / 40), (-81 / 40), (-13 / 8), (31 / 40), (5 / 8), (-3 / 8)]) ((11878261 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly005 :
    |polyEval (![(-11 / 20), (-17 / 40), (16 / 5), (-173 / 40), (-27 / 4), (13 / 40), 5, (-19 / 8)]) u| ≤ ((7472193 / 12500000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-11 / 20), (-17 / 40), (16 / 5), (-173 / 40), (-27 / 4), (13 / 40), 5, (-19 / 8)]) ((7472193 / 12500000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly006 :
    |polyEval (![(-11 / 20), (1 / 5), (79 / 20), (-7 / 10), (-11 / 4), (1 / 5), (5 / 4), (-1 / 2)]) u| ≤ ((559979 / 20000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-11 / 20), (1 / 5), (79 / 20), (-7 / 10), (-11 / 4), (1 / 5), (5 / 4), (-1 / 2)]) ((559979 / 20000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly007 :
    |polyEval (![(-43 / 80), (-73 / 80), (87 / 80), (53 / 80), (-9 / 16), (-23 / 80), (5 / 16), (-1 / 16)]) u| ≤ ((70460817 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-43 / 80), (-73 / 80), (87 / 80), (53 / 80), (-9 / 16), (-23 / 80), (5 / 16), (-1 / 16)]) ((70460817 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
