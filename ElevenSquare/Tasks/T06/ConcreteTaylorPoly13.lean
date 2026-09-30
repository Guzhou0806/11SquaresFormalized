import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly052 :
    |polyEval (![(161 / 400), (771 / 400), (-1549 / 400), (729 / 400), (419 / 80), (581 / 400), (-75 / 16), (147 / 80)]) u| ≤ ((7722539 / 10000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(161 / 400), (771 / 400), (-1549 / 400), (729 / 400), (419 / 80), (581 / 400), (-75 / 16), (147 / 80)]) ((7722539 / 10000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly053 :
    |polyEval (![(11 / 25), (-357 / 200), (1 / 25), (-643 / 200), (-11 / 5), (-27 / 200), (5 / 2), (-49 / 40)]) u| ≤ ((40022153 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(11 / 25), (-357 / 200), (1 / 25), (-643 / 200), (-11 / 5), (-27 / 200), (5 / 2), (-49 / 40)]) ((40022153 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly054 :
    |polyEval (![(9 / 20), (1 / 5), (-1 / 20), (71 / 20), (3 / 4), (-3 / 10), (-5 / 4), (3 / 4)]) u| ≤ ((69930841 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(9 / 20), (1 / 5), (-1 / 20), (71 / 20), (3 / 4), (-3 / 10), (-5 / 4), (3 / 4)]) ((69930841 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly055 :
    |polyEval (![(181 / 400), (691 / 400), (-1529 / 400), (-691 / 400), (359 / 80), (701 / 400), (-55 / 16), (87 / 80)]) u| ≤ ((57294549 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(181 / 400), (691 / 400), (-1529 / 400), (-691 / 400), (359 / 80), (701 / 400), (-55 / 16), (87 / 80)]) ((57294549 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
