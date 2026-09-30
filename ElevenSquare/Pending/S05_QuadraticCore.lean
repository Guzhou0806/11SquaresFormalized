import ElevenSquare.Pending.Types
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact interval positivity and rational half-angle core bounds. -/

namespace ElevenSquare.Pending
noncomputable section

-- Endpoint/minimum tests sufficient for strict positivity of a quadratic.
theorem quadratic_positive_on_closed_interval
    (a b c l u : ℝ) (hlu : l ≤ u)
    (hl : 0 < Quadratic a b c l) (hu : 0 < Quadratic a b c u)
    (hv : 0 < a → l ≤ -b/(2*a) → -b/(2*a) ≤ u →
      0 < Quadratic a b c (-b/(2*a))) :
    ∀ t ∈ Set.Icc l u, 0 < Quadratic a b c t := by
  intro t ht
  have diff (x y : ℝ) : Quadratic a b c y - Quadratic a b c x =
      (y-x)*(a*(y+x)+b) := by unfold Quadratic; ring
  by_cases ha : 0 < a
  · let v := -b/(2*a)
    have hstat : 2*a*v+b = 0 := by
      dsimp [v]
      field_simp
      <;> ring
    by_cases hvl : v < l
    · have hc : 0 ≤ a*(t+l)+b := by
        nlinarith [mul_nonneg ha.le (show 0 ≤ t+l-2*v by linarith [ht.1])]
      have hdiff := mul_nonneg (sub_nonneg.mpr ht.1) hc
      rw [← diff l t] at hdiff
      linarith
    · by_cases huv : u < v
      · have hc : a*(u+t)+b ≤ 0 := by
          nlinarith [mul_nonneg ha.le (show 0 ≤ 2*v-(u+t) by linarith [ht.2])]
        have hdiff := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hc
        rw [← diff t u] at hdiff
        linarith
      · have hpos : 0 < Quadratic a b c v := hv ha (le_of_not_gt hvl) (le_of_not_gt huv)
        have hb : b = -2*a*v := by linarith
        have heq : Quadratic a b c t - Quadratic a b c v = a*(t-v)^2 := by
          rw [hb]
          unfold Quadratic
          ring
        have hnonneg := mul_nonneg ha.le (sq_nonneg (t-v))
        rw [← heq] at hnonneg
        linarith
  · have han : a ≤ 0 := le_of_not_gt ha
    by_cases hc : 0 ≤ a*(t+l)+b
    · have hdiff := mul_nonneg (sub_nonneg.mpr ht.1) hc
      rw [← diff l t] at hdiff
      linarith
    · have hcu : a*(u+t)+b ≤ 0 := by
        nlinarith [mul_nonpos_of_nonpos_of_nonneg han (sub_nonneg.mpr hlu)]
      have hdiff := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hcu
      rw [← diff t u] at hdiff
      linarith

-- Multiplying by 1+t² preserves the strict open-square inequalities.
theorem half_angle_core_projection
    (v : Point) (t : ℝ)
    (hx : |(1-t^2)*v.1+2*t*v.2| < (1+t^2)/2)
    (hy : |-2*t*v.1+(1-t^2)*v.2| < (1+t^2)/2) :
    |dot v (chartAxis t)| < 1/2 ∧ |dot v (perp (chartAxis t))| < 1/2 := by
  have hd : 0 < 1+t^2 := by positivity
  have hx' : |((1-t^2)*v.1+2*t*v.2)/(1+t^2)| < 1/2 := by
    rw [abs_div, abs_of_pos hd]
    apply (div_lt_iff hd).mpr
    nlinarith [hx]
  have hy' : |(-2*t*v.1+(1-t^2)*v.2)/(1+t^2)| < 1/2 := by
    rw [abs_div, abs_of_pos hd]
    apply (div_lt_iff hd).mpr
    nlinarith [hy]
  have ex : dot v (chartAxis t) = ((1-t^2)*v.1+2*t*v.2)/(1+t^2) := by
    dsimp [dot, chartAxis]
    ring
  have ey : dot v (perp (chartAxis t)) = (-2*t*v.1+(1-t^2)*v.2)/(1+t^2) := by
    dsimp [dot, chartAxis, perp]
    ring
  exact ⟨ex ▸ hx', ey ▸ hy'⟩


end
end ElevenSquare.Pending
