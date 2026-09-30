import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly060 :
    |polyEval (![(107 / 200), (-6 / 25), (-363 / 200), (131 / 25), (153 / 40), (-16 / 25), (-25 / 8), (8 / 5)]) u| ≤ ((25950207 / 50000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(107 / 200), (-6 / 25), (-363 / 200), (131 / 25), (153 / 40), (-16 / 25), (-25 / 8), (8 / 5)]) ((25950207 / 50000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly061 :
    |polyEval (![(43 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)]) u| ≤ ((70460817 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(43 / 80), (73 / 80), (-87 / 80), (-53 / 80), (9 / 16), (23 / 80), (-5 / 16), (1 / 16)]) ((70460817 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly062 :
    |polyEval (![(11 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)]) u| ≤ ((114521687 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(11 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)]) ((114521687 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly063 :
    |polyEval (![(3 / 5), (-31 / 40), (31 / 10), (-139 / 40), -5, (-41 / 40), 5, (-17 / 8)]) u| ≤ ((47512547 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(3 / 5), (-31 / 40), (31 / 10), (-139 / 40), -5, (-41 / 40), 5, (-17 / 8)]) ((47512547 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
