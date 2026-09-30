import ElevenSquare.Pending.Types
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Exact rational-endpoint bounds for the whole closed half-angle interval. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem chartAxis_first_antitone {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (chartAxis b).1 ≤ (chartAxis a).1 := by
  have hsq : a^2 ≤ b^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (add_nonneg ha (ha.trans hab))]
  have hda : 0 < 1+a^2 := by positivity
  have hdb : 0 < 1+b^2 := by positivity
  dsimp [chartAxis]
  apply (div_le_div_iff₀ hdb hda).mpr
  nlinarith

theorem chartAxis_second_monotone {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (chartAxis a).2 ≤ (chartAxis b).2 := by
  have hb0 : 0 ≤ b := ha.trans hab
  have habprod : a*b ≤ 1 := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hb)]
  have hprod : 0 ≤ (b-a)*(1-a*b) :=
    mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr habprod)
  have hda : 0 < 1+a^2 := by positivity
  have hdb : 0 < 1+b^2 := by positivity
  dsimp [chartAxis]
  apply (div_le_div_iff₀ hda hdb).mpr
  nlinarith

end
end ElevenSquare.Tasks.T07
