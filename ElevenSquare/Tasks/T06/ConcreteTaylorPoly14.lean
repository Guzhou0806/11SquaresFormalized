import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly056 :
    |polyEval (![(19 / 40), (-21 / 40), (49 / 40), (-159 / 40), (-43 / 8), (9 / 40), (35 / 8), (-17 / 8)]) u| ≤ ((4155601 / 25000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(19 / 40), (-21 / 40), (49 / 40), (-159 / 40), (-43 / 8), (9 / 40), (35 / 8), (-17 / 8)]) ((4155601 / 25000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly057 :
    |polyEval (![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)]) u| ≤ ((5939131 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(39 / 80), (-81 / 80), (-71 / 80), (81 / 80), (13 / 16), (-31 / 80), (-5 / 16), (3 / 16)]) ((5939131 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly058 :
    |polyEval (![(1 / 2), 0, 0, 0, 0, 0, 0, 0]) u| ≤ ((1 / 2) : ℝ) := by
  have h := concrete_poly_abs_bound (![(1 / 2), 0, 0, 0, 0, 0, 0, 0]) ((1 / 2))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly059 :
    |polyEval (![(21 / 40), (-89 / 40), (-69 / 40), (-61 / 40), (7 / 8), (-19 / 40), (5 / 8), (-3 / 8)]) u| ≤ ((58052581 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(21 / 40), (-89 / 40), (-69 / 40), (-61 / 40), (7 / 8), (-19 / 40), (5 / 8), (-3 / 8)]) ((58052581 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
