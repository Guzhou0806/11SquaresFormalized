import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly016 :
    |polyEval (![(-161 / 400), (-771 / 400), (1549 / 400), (-729 / 400), (-419 / 80), (-581 / 400), (75 / 16), (-147 / 80)]) u| ≤ ((7722539 / 10000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-161 / 400), (-771 / 400), (1549 / 400), (-729 / 400), (-419 / 80), (-581 / 400), (75 / 16), (-147 / 80)]) ((7722539 / 10000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly017 :
    |polyEval (![(-3 / 8), (5 / 4), (39 / 8), (-11 / 2), (-53 / 8), (-1 / 4), (45 / 8), (-5 / 2)]) u| ≤ ((17817143 / 50000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-3 / 8), (5 / 4), (39 / 8), (-11 / 2), (-53 / 8), (-1 / 4), (45 / 8), (-5 / 2)]) ((17817143 / 50000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly018 :
    |polyEval (![(-147 / 400), (-867 / 400), (823 / 400), (1367 / 400), (-113 / 80), (-837 / 400), (25 / 16), (-19 / 80)]) u| ≤ ((75324977 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-147 / 400), (-867 / 400), (823 / 400), (1367 / 400), (-113 / 80), (-837 / 400), (25 / 16), (-19 / 80)]) ((75324977 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly019 :
    |polyEval (![(-7 / 20), (23 / 20), (29 / 10), (-103 / 20), (-21 / 4), (-7 / 20), 5, (-9 / 4)]) u| ≤ ((6017117 / 50000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-7 / 20), (23 / 20), (29 / 10), (-103 / 20), (-21 / 4), (-7 / 20), 5, (-9 / 4)]) ((6017117 / 50000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
