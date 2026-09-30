import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly044 :
    |polyEval (![(9 / 80), (19 / 80), (319 / 80), (-359 / 80), (-93 / 16), (-51 / 80), (85 / 16), (-37 / 16)]) u| ≤ ((41573417 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(9 / 80), (19 / 80), (319 / 80), (-359 / 80), (-93 / 16), (-51 / 80), (85 / 16), (-37 / 16)]) ((41573417 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly045 :
    |polyEval (![(3 / 25), (-159 / 50), (117 / 100), (443 / 100), (-3 / 5), (-62 / 25), (5 / 4), (-1 / 20)]) u| ≤ ((69385847 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(3 / 25), (-159 / 50), (117 / 100), (443 / 100), (-3 / 5), (-62 / 25), (5 / 4), (-1 / 20)]) ((69385847 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly046 :
    |polyEval (![(11 / 80), (11 / 80), (161 / 80), (-331 / 80), (-71 / 16), (-59 / 80), (75 / 16), (-33 / 16)]) u| ≤ ((4493341 / 25000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(11 / 80), (11 / 80), (161 / 80), (-331 / 80), (-71 / 16), (-59 / 80), (75 / 16), (-33 / 16)]) ((4493341 / 25000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly047 :
    |polyEval (![(17 / 100), (-169 / 50), (61 / 50), (22 / 25), (-27 / 20), (-109 / 50), (5 / 2), (-4 / 5)]) u| ≤ ((5582293 / 6250000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(17 / 100), (-169 / 50), (61 / 50), (22 / 25), (-27 / 20), (-109 / 50), (5 / 2), (-4 / 5)]) ((5582293 / 6250000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
