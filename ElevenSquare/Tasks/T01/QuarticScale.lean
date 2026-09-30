import ElevenSquare.Tasks.T01.QuarticBernstein

namespace ElevenSquare.Tasks.T01
noncomputable section

/-- Positive rational normalization lets many certificates share one polynomial. -/
def Quartic.scale (r : ℚ) (p : Quartic) : Quartic :=
  ⟨r*p.c0, r*p.c1, r*p.c2, r*p.c3, r*p.c4⟩

theorem quartic_scale_eval (r : ℚ) (p : Quartic) (t : ℝ) :
    (p.scale r).eval t = (r : ℝ) * p.eval t := by
  dsimp [Quartic.scale, Quartic.eval]
  push_cast
  ring

theorem quartic_scale_nonneg (r : ℚ) (p : Quartic) (t : ℝ)
    (hr : 0 ≤ r) (hp : 0 ≤ p.eval t) : 0 ≤ (p.scale r).eval t := by
  rw [quartic_scale_eval]
  exact mul_nonneg (by exact_mod_cast hr) hp

theorem quartic_scale_pos (r : ℚ) (p : Quartic) (t : ℝ)
    (hr : 0 < r) (hp : 0 < p.eval t) : 0 < (p.scale r).eval t := by
  rw [quartic_scale_eval]
  exact mul_pos (by exact_mod_cast hr) hp

/-- The chart denominator is positive for every real angle parameter. -/
theorem chart_denominator_quartic_pos (t : ℝ) :
    0 < (⟨1, 0, 1, 0, 0⟩ : Quartic).eval t := by
  norm_num [Quartic.eval]
  positivity

theorem chart_parameter_quartic_nonneg (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (⟨0, 1, 0, 0, 0⟩ : Quartic).eval t := by
  simpa [Quartic.eval] using ht

theorem chart_parameter_quartic_pos (t : ℝ) (ht : 0 < t) :
    0 < (⟨0, 1, 0, 0, 0⟩ : Quartic).eval t := by
  simpa [Quartic.eval] using ht

theorem chart_cosine_quartic_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (⟨1, 0, -1, 0, 0⟩ : Quartic).eval t := by
  norm_num [Quartic.eval]
  simpa only [abs_of_nonneg ht0] using ht1

theorem chart_cosine_quartic_pos (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < (⟨1, 0, -1, 0, 0⟩ : Quartic).eval t := by
  norm_num [Quartic.eval]
  simpa only [abs_of_nonneg ht0] using ht1

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.quartic_scale_pos
#print axioms ElevenSquare.Tasks.T01.chart_denominator_quartic_pos
