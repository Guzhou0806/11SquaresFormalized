import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly028 :
    |polyEval (![(-3 / 80), (97 / 80), (67 / 80), (203 / 80), (-1 / 16), (7 / 80), (-15 / 16), (9 / 16)]) u| ≤ ((63991711 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-3 / 80), (97 / 80), (67 / 80), (203 / 80), (-1 / 16), (7 / 80), (-15 / 16), (9 / 16)]) ((63991711 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly029 :
    |polyEval (![(-3 / 80), (127 / 80), (-493 / 80), (253 / 80), (111 / 16), (97 / 80), (-95 / 16), (39 / 16)]) u| ≤ ((651783 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-3 / 80), (127 / 80), (-493 / 80), (253 / 80), (111 / 16), (97 / 80), (-95 / 16), (39 / 16)]) ((651783 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly030 :
    |polyEval (![(-1 / 40), (-63 / 20), (9 / 40), (73 / 20), (5 / 8), (-73 / 20), (15 / 8), (-1 / 4)]) u| ≤ ((24422397 / 25000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-1 / 40), (-63 / 20), (9 / 40), (73 / 20), (5 / 8), (-73 / 20), (15 / 8), (-1 / 4)]) ((24422397 / 25000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly031 :
    |polyEval (![(-1 / 40), (-21 / 40), (49 / 40), (-159 / 40), (-43 / 8), (9 / 40), (35 / 8), (-17 / 8)]) u| ≤ ((33377597 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-1 / 40), (-21 / 40), (49 / 40), (-159 / 40), (-43 / 8), (9 / 40), (35 / 8), (-17 / 8)]) ((33377597 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
