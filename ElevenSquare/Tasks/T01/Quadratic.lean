import ElevenSquare.Pending.S05_Trace
import Mathlib.Tactic.FieldSimp

/-!
# A checked quadratic/core interface for baseline certificate rows

The finite check consists of endpoint values and a concavity, monotonicity,
or strictly positive discriminant-margin witness. All comparisons are exact.
No endpoint-only argument is used for a convex quadratic with an interior
minimum. This file does not use the pending S05 quadratic/core contracts.
-/

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

def baselineQuadratic (a b c t : ℝ) : ℝ := a*t^2 + b*t + c

def BaselineQuadraticCheck (a b c l u : ℚ) : Prop :=
  0 < a*l^2 + b*l + c ∧ 0 < a*u^2 + b*u + c ∧
  (a ≤ 0 ∨ 0 ≤ b + 2*a*l ∨ b + 2*a*u ≤ 0 ∨ 0 < 4*a*c-b^2)

instance (a b c l u : ℚ) : Decidable (BaselineQuadraticCheck a b c l u) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ∨ _ ∨ _ ∨ _)))

theorem baseline_quadratic_positive (a b c l u t : ℝ)
    (hlt : l ≤ t) (htu : t ≤ u)
    (hl : 0 < baselineQuadratic a b c l)
    (hu : 0 < baselineQuadratic a b c u)
    (hc : a ≤ 0 ∨ 0 ≤ b + 2*a*l ∨ b + 2*a*u ≤ 0 ∨ 0 < 4*a*c-b^2) :
    0 < baselineQuadratic a b c t := by
  by_cases hlu : l = u
  · have ht : t = l := le_antisymm (hlu ▸ htu) hlt
    simpa only [ht] using hl
  have hwidth : 0 < u-l := sub_pos.mpr (lt_of_le_of_ne (hlt.trans htu) hlu)
  by_cases ha : a ≤ 0
  · have hn := mul_nonneg (neg_nonneg.mpr ha)
      (mul_nonneg (sub_nonneg.mpr hlt) (sub_nonneg.mpr htu))
    have hw : 0 < (u-t) * baselineQuadratic a b c l +
        (t-l) * baselineQuadratic a b c u := by
      by_cases ht : t = u
      · subst t
        simpa using mul_pos hwidth hu
      · have hh : 0 < u-t := sub_pos.mpr (lt_of_le_of_ne htu ht)
        exact add_pos_of_pos_of_nonneg (mul_pos hh hl)
          (mul_nonneg (sub_nonneg.mpr hlt) hu.le)
    have hn' := mul_nonneg hwidth.le hn
    have he : (u-l) * baselineQuadratic a b c t =
        (u-t)*baselineQuadratic a b c l + (t-l)*baselineQuadratic a b c u +
        (u-l) * ((-a) * ((t-l)*(u-t))) := by
      dsimp [baselineQuadratic]
      ring
    have hm : 0 < (u-l) * baselineQuadratic a b c t := by rw [he]; linarith
    exact (mul_pos_iff_of_pos_left hwidth).mp hm
  have hap : 0 < a := lt_of_not_ge ha
  rcases hc with h | h | h | h
  · exact False.elim (ha h)
  · have hi : 0 ≤ a*(t+l)+b := by
      have hn := mul_nonneg hap.le (sub_nonneg.mpr hlt)
      nlinarith
    have hm := mul_nonneg (sub_nonneg.mpr hlt) hi
    dsimp [baselineQuadratic] at hl ⊢
    nlinarith
  · have hi : a*(t+u)+b ≤ 0 := by
      have hn := mul_nonpos_of_nonneg_of_nonpos hap.le (sub_nonpos.mpr htu)
      nlinarith
    have hm := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr htu) hi
    dsimp [baselineQuadratic] at hu ⊢
    nlinarith
  · by_contra ht
    have hn := mul_nonpos_of_nonneg_of_nonpos hap.le (not_lt.mp ht)
    dsimp [baselineQuadratic] at hn
    nlinarith [sq_nonneg (2*a*t+b)]

theorem baseline_quadratic_check_sound (a b c l u : ℚ)
    (h : BaselineQuadraticCheck a b c l u) (t : ℝ)
    (hl : (l : ℝ) ≤ t) (hu : t ≤ (u : ℝ)) :
    0 < baselineQuadratic a b c t := by
  rcases h with ⟨ha, hb, hc⟩
  apply baseline_quadratic_positive (a:ℝ) (b:ℝ) (c:ℝ) (l:ℝ) (u:ℝ) t hl hu
  · dsimp [baselineQuadratic]; exact_mod_cast ha
  · dsimp [baselineQuadratic]; exact_mod_cast hb
  · exact_mod_cast hc

/-- Four strict quadratic checks, for both signs of both local projections. -/
def BaselineCoreVertexCheck (v : QPoint) (l u : ℚ) : Prop :=
  BaselineQuadraticCheck (1/2+v.1) (-2*v.2) (1/2-v.1) l u ∧
  BaselineQuadraticCheck (1/2-v.1) (2*v.2) (1/2+v.1) l u ∧
  BaselineQuadraticCheck (1/2+v.2) (2*v.1) (1/2-v.2) l u ∧
  BaselineQuadraticCheck (1/2-v.2) (-2*v.1) (1/2+v.2) l u

instance (v : QPoint) (l u : ℚ) : Decidable (BaselineCoreVertexCheck v l u) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem baseline_core_vertex_check_sound (q : UnitSquare) (v : QPoint) (l u : ℚ)
    (h : BaselineCoreVertexCheck v l u) (t : ℝ)
    (hl : (l:ℝ) ≤ t) (hu : t ≤ (u:ℝ)) (hq : q.axis = chartAxis t) :
    OpenSquare q (q.center + realPoint v) := by
  have h1 := baseline_quadratic_check_sound _ _ _ _ _ h.1 t hl hu
  have h2 := baseline_quadratic_check_sound _ _ _ _ _ h.2.1 t hl hu
  have h3 := baseline_quadratic_check_sound _ _ _ _ _ h.2.2.1 t hl hu
  have h4 := baseline_quadratic_check_sound _ _ _ _ _ h.2.2.2 t hl hu
  dsimp only [baselineQuadratic] at h1 h2 h3 h4
  push_cast at h1 h2 h3 h4
  have hd : 0 < 1+t^2 := by nlinarith [sq_nonneg t]
  have hx : localX q (q.center + realPoint v) * (1+t^2) =
      (v.1:ℝ)*(1-t^2) + 2*(v.2:ℝ)*t := by
    simp only [localX, add_sub_cancel_left, hq, dot, chartAxis, realPoint]
    field_simp [ne_of_gt hd]
    ring
  have hy : localY q (q.center + realPoint v) * (1+t^2) =
      (v.2:ℝ)*(1-t^2) - 2*(v.1:ℝ)*t := by
    simp only [localY, add_sub_cancel_left, hq, dot, chartAxis, realPoint, perp]
    field_simp [ne_of_gt hd]
    ring
  have bound (z r : ℝ) (hz : z*(1+t^2)=r)
      (hm : 0 < (1+t^2)/2-r) (hp : 0 < (1+t^2)/2+r) : |z| < 1/2 := by
    apply abs_lt.mpr
    constructor
    · apply (mul_lt_mul_right hd).mp
      rw [hz]
      linarith
    · apply (mul_lt_mul_right hd).mp
      rw [hz]
      linarith
  constructor
  · apply bound _ _ hx <;> nlinarith
  · apply bound _ _ hy <;> nlinarith

theorem baseline_common_core_hull (Q : List QPoint) (q : UnitSquare)
    (hv : ∀ v ∈ Q, OpenSquare q (q.center + realPoint v)) :
    CoreFits (rationalHull Q) q := by
  have hc := (openSquare_convex q).translate_preimage_right q.center
  have hh : rationalHull Q ⊆ {v | OpenSquare q (q.center+v)} := by
    apply convexHull_min _ hc
    rintro p ⟨v, hv', rfl⟩
    exact hv v hv'
  exact hh

theorem baseline_row_core_checked (r : PoseRow) (Q : List QPoint)
    (h : ∀ v ∈ Q, BaselineCoreVertexCheck v r.lo r.hi) (q : UnitSquare)
    (hq : r.contains q) : CoreFits (rationalHull Q) q := by
  obtain ⟨t, _, _, hl, hu, ha⟩ := hq.2
  apply baseline_common_core_hull
  intro v hv
  exact baseline_core_vertex_check_sound q v r.lo r.hi (h v hv) t hl hu ha

end
end ElevenSquare.Tasks.T01
