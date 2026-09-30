import ElevenSquare.Tasks.T01.Wall

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

theorem corner_cross_envelope (a b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    a * (1 - (a+b)/2) + b/3 ≤ 1/2 := by
  by_cases ha : 2/3 ≤ a
  · have hm := mul_nonneg hb0 (sub_nonneg.mpr ha)
    nlinarith [sq_nonneg (1-a)]
  · have hm := mul_nonneg (sub_nonneg.mpr hb1)
      (sub_nonneg.mpr (le_of_not_ge ha))
    nlinarith [sq_nonneg (a-1/2)]

theorem corner_mixed_bound (a b x y : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hx : x < 1-(a+b)/2) (hy : -(1/3) ≤ y) :
    a*x-b*y < 1/2 := by
  by_cases haz : a = 0
  · subst a
    have h := mul_le_mul_of_nonneg_left hy hb
    nlinarith
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    have h := mul_lt_mul_of_pos_left hx hap
    have h' := mul_le_mul_of_nonneg_left hy hb
    have he := corner_cross_envelope a b hb hb1
    nlinarith

/-- A rectangle adapted to the two lower container walls lies inside every
charted unit square. This avoids an angle subdivision for corner seed points. -/
theorem corner_coordinate_bounds (a b x y : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : a^2+b^2=1)
    (hx0 : -(1/3) ≤ x) (hy0 : -(1/3) ≤ y)
    (hx1 : x < 1-(a+b)/2) (hy1 : y < 1-(a+b)/2) :
    |a*x+b*y| < 1/2 ∧ |-b*x+a*y| < 1/2 := by
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg b]
  have hb1 : b ≤ 1 := by nlinarith [sq_nonneg a]
  have hsum : a+b < 3/2 := by nlinarith [sq_nonneg (a-b)]
  have hpos : 0 < a+b := by nlinarith
  have hxlo := mul_le_mul_of_nonneg_left hx0 ha
  have hylo := mul_le_mul_of_nonneg_left hy0 hb
  have hlow : -(1/2) < a*x+b*y := by nlinarith
  have hstrict : a*x+b*y < (a+b)*(1-(a+b)/2) := by
    by_cases haz : a = 0
    · have hbp : 0 < b := by linarith
      have h := mul_lt_mul_of_pos_left hy1 hbp
      simpa [haz] using h
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
      have h := mul_lt_mul_of_pos_left hx1 hap
      have h' := mul_le_mul_of_nonneg_left hy1.le hb
      nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)
  have hupper : a*x+b*y < 1/2 := by nlinarith
  have hmix1 := corner_mixed_bound a b y x ha hb hb1 hy1 hx0
  have hmix2 := corner_mixed_bound b a x y hb ha ha1 (by simpa [add_comm] using hx1) hy0
  exact ⟨abs_lt.mpr ⟨hlow,hupper⟩, abs_lt.mpr ⟨by linarith, by linarith⟩⟩

/-- Only two closed-cell coordinate bounds and the actual container walls are
needed. The owned point has strict coordinate bounds below one. -/
theorem corner_point_owned (q : UnitSquare) (p : Point)
    (hcont : ∀ z, ClosedSquare q z → InContainer coverCap z)
    (ha : 0 ≤ q.axis.1) (hb : 0 ≤ q.axis.2)
    (hpx : p.1 < 1) (hpy : p.2 < 1)
    (hcx : q.center.1 ≤ p.1+1/3) (hcy : q.center.2 ≤ p.2+1/3) :
    OpenSquare q p := by
  have hw := baseline_contained_axis_bounds q coverCap hcont
  have hu := q.axis_unit
  dsimp [normSq, dot] at hu
  have hh := corner_coordinate_bounds q.axis.1 q.axis.2
    (p.1-q.center.1) (p.2-q.center.2) ha hb (by nlinarith [hu])
    (by linarith) (by linarith) (by linarith [hw.1]) (by linarith [hw.2.2.1])
  simpa [OpenSquare, localX, localY, dot, perp, mul_comm] using hh

end
end ElevenSquare.Tasks.T01
