import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly000 :
    |polyEval (![(-61 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)]) u| ≤ ((31599987 / 25000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-61 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)]) ((31599987 / 25000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly001 :
    |polyEval (![(-83 / 80), (-73 / 80), (87 / 80), (53 / 80), (-9 / 16), (-23 / 80), (5 / 16), (-1 / 16)]) u| ≤ ((120460817 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-83 / 80), (-73 / 80), (87 / 80), (53 / 80), (-9 / 16), (-23 / 80), (5 / 16), (-1 / 16)]) ((120460817 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly002 :
    |polyEval (![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)]) u| ≤ ((19099987 / 25000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-41 / 40), (1 / 10), (79 / 40), (-7 / 20), (-11 / 8), (1 / 10), (5 / 8), (-1 / 4)]) ((19099987 / 25000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly003 :
    |polyEval (![-1, 0, 0, 0, 0, 0, 0, 0]) u| ≤ (1 : ℝ) := by
  have h := concrete_poly_abs_bound (![-1, 0, 0, 0, 0, 0, 0, 0]) (1)
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
