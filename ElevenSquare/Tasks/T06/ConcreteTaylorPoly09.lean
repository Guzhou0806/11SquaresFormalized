import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly036 :
    |polyEval (![(3 / 80), (-97 / 80), (-67 / 80), (-203 / 80), (1 / 16), (-7 / 80), (15 / 16), (-9 / 16)]) u| ≤ ((63991711 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(3 / 80), (-97 / 80), (-67 / 80), (-203 / 80), (1 / 16), (-7 / 80), (15 / 16), (-9 / 16)]) ((63991711 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly037 :
    |polyEval (![(19 / 400), (309 / 400), (-371 / 400), (1691 / 400), (241 / 80), (-101 / 400), (-45 / 16), (113 / 80)]) u| ≤ ((45961283 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(19 / 400), (309 / 400), (-371 / 400), (1691 / 400), (241 / 80), (-101 / 400), (-45 / 16), (113 / 80)]) ((45961283 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly038 :
    |polyEval (![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)]) u| ≤ ((64521687 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(1 / 20), (77 / 40), (-1 / 5), (-67 / 40), (-1 / 4), (27 / 40), 0, (-1 / 8)]) ((64521687 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly039 :
    |polyEval (![(1 / 16), (-27 / 16), (67 / 16), (-45 / 16), (-89 / 16), (-21 / 16), (85 / 16), (-35 / 16)]) u| ≤ ((22948271 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(1 / 16), (-27 / 16), (67 / 16), (-45 / 16), (-89 / 16), (-21 / 16), (85 / 16), (-35 / 16)]) ((22948271 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
