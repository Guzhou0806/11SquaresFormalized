import ElevenSquare.Tasks.T06.ConcreteTaylorPolynomialBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section
set_option maxHeartbeats 4000000

theorem concrete_abs_poly020 :
    |polyEval (![(-117 / 400), (-987 / 400), (53 / 400), (87 / 400), (-63 / 80), (-757 / 400), (35 / 16), (-59 / 80)]) u| ≤ ((118855871 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-117 / 400), (-987 / 400), (53 / 400), (87 / 400), (-63 / 80), (-757 / 400), (35 / 16), (-59 / 80)]) ((118855871 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly021 :
    |polyEval (![(-73 / 400), (-903 / 400), (1157 / 400), (-1697 / 400), (-467 / 80), (-33 / 400), (75 / 16), (-171 / 80)]) u| ≤ ((46226271 / 50000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-73 / 400), (-903 / 400), (1157 / 400), (-1697 / 400), (-467 / 80), (-33 / 400), (75 / 16), (-171 / 80)]) ((46226271 / 50000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly022 :
    |polyEval (![(-11 / 80), (-11 / 80), (-161 / 80), (331 / 80), (71 / 16), (59 / 80), (-75 / 16), (33 / 16)]) u| ≤ ((4493341 / 25000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-11 / 80), (-11 / 80), (-161 / 80), (331 / 80), (71 / 16), (59 / 80), (-75 / 16), (33 / 16)]) ((4493341 / 25000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num

theorem concrete_abs_poly023 :
    |polyEval (![(-9 / 80), (-19 / 80), (-319 / 80), (359 / 80), (93 / 16), (51 / 80), (-85 / 16), (37 / 16)]) u| ≤ ((41573417 / 100000000) : ℝ) := by
  have h := concrete_poly_abs_bound (![(-9 / 80), (-19 / 80), (-319 / 80), (359 / 80), (93 / 16), (51 / 80), (-85 / 16), (37 / 16)]) ((41573417 / 100000000))
    (by norm_num [polyLower, Fin.sum_univ_succ])
    (by norm_num [polyUpper, Fin.sum_univ_succ])
  convert h using 1 <;> norm_num


end
end ElevenSquare.Tasks.T06
