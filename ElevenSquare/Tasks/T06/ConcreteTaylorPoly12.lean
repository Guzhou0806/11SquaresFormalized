import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly048 :
    |polyEval (![(39 / 200), (-87 / 25), (-151 / 200), (123 / 100), (1 / 40), (-57 / 25), (15 / 8), (-11 / 20)]) u| ≤ ((5645837 / 5000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(39 / 200), (-87 / 25), (-151 / 200), (123 / 100), (1 / 40), (-57 / 25), (15 / 8), (-11 / 20)]) ((5645837 / 5000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly049 :
    |polyEval (![(61 / 200), (-327 / 100), (401 / 200), (-323 / 100), (-201 / 40), (-47 / 100), (35 / 8), (-39 / 20)]) u| ≤ ((21628353 / 25000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(61 / 200), (-327 / 100), (401 / 200), (-323 / 100), (-201 / 40), (-47 / 100), (35 / 8), (-39 / 20)]) ((21628353 / 25000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly050 :
    |polyEval (![(127 / 400), (947 / 400), (-843 / 400), (53 / 400), (173 / 80), (717 / 400), (-45 / 16), (79 / 80)]) u| ≤ ((47627909 / 50000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(127 / 400), (947 / 400), (-843 / 400), (53 / 400), (173 / 80), (717 / 400), (-45 / 16), (79 / 80)]) ((47627909 / 50000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly051 :
    |polyEval (![(147 / 400), (867 / 400), (-823 / 400), (-1367 / 400), (113 / 80), (837 / 400), (-25 / 16), (19 / 80)]) u| ≤ ((75324977 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(147 / 400), (867 / 400), (-823 / 400), (-1367 / 400), (113 / 80), (837 / 400), (-25 / 16), (19 / 80)]) ((75324977 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
