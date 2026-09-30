import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly008 :
    |polyEval (![(-41 / 80), (-171 / 80), (89 / 80), (211 / 80), (-3 / 16), (-261 / 80), (35 / 16), (-7 / 16)]) u| ≤ ((103628719 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-41 / 80), (-171 / 80), (89 / 80), (211 / 80), (-3 / 16), (-261 / 80), (35 / 16), (-7 / 16)]) ((103628719 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly009 :
    |polyEval (![(-1 / 2), 0, 0, 0, 0, 0, 0, 0]) u| ≤ ((1 / 2) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-1 / 2), 0, 0, 0, 0, 0, 0, 0]) ((1 / 2))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly010 :
    |polyEval (![(-39 / 80), (81 / 80), (71 / 80), (-81 / 80), (-13 / 16), (31 / 80), (5 / 16), (-3 / 16)]) u| ≤ ((5939131 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-39 / 80), (81 / 80), (71 / 80), (-81 / 80), (-13 / 16), (31 / 80), (5 / 16), (-3 / 16)]) ((5939131 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly011 :
    |polyEval (![(-19 / 40), (81 / 40), (71 / 40), (-81 / 40), (-13 / 8), (31 / 40), (5 / 8), (-3 / 8)]) u| ≤ ((1906087 / 5000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-19 / 40), (81 / 40), (71 / 40), (-81 / 40), (-13 / 8), (31 / 40), (5 / 8), (-3 / 8)]) ((1906087 / 5000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
