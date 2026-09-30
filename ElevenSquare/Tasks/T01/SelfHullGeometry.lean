import ElevenSquare.Tasks.T01.Wall
import ElevenSquare.Tasks.T01.ConvexWitnesses

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

def NonnegativeQuadraticCheck (a b c l u : ℚ) : Prop :=
  0 ≤ a*l^2+b*l+c ∧ 0 ≤ a*u^2+b*u+c ∧
    (a ≤ 0 ∨ 0 ≤ b+2*a*l ∨ b+2*a*u ≤ 0 ∨ 0 ≤ 4*a*c-b^2)

instance nonnegativeQuadraticCheckDecidable (a b c l u : ℚ) :
    Decidable (NonnegativeQuadraticCheck a b c l u) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ∨ _ ∨ _ ∨ _)))

theorem nonnegative_quadratic_check_sound (a b c l u : ℚ)
    (hc : NonnegativeQuadraticCheck a b c l u) (t : ℝ)
    (hl : (l : ℝ) ≤ t) (hu : t ≤ (u : ℝ)) :
    0 ≤ (a : ℝ)*t^2+(b : ℝ)*t+c := by
  have hleft : 0 ≤ (a : ℝ)*(l : ℝ)^2+(b : ℝ)*(l : ℝ)+c := by exact_mod_cast hc.1
  have hright : 0 ≤ (a : ℝ)*(u : ℝ)^2+(b : ℝ)*(u : ℝ)+c := by exact_mod_cast hc.2.1
  have hcases : (a : ℝ) ≤ 0 ∨ 0 ≤ (b : ℝ)+2*(a : ℝ)*(l : ℝ) ∨
      (b : ℝ)+2*(a : ℝ)*(u : ℝ) ≤ 0 ∨ 0 ≤ 4*(a : ℝ)*(c : ℝ)-(b : ℝ)^2 := by
    exact_mod_cast hc.2.2
  by_cases ha : (a : ℝ) ≤ 0
  · exact baseline_concave_quadratic_nonneg a b c l u t ha hl hu hleft hright
  have hap : 0 < (a : ℝ) := lt_of_not_ge ha
  rcases hcases with h | h | h | h
  · exact False.elim (ha h)
  · have hm := mul_nonneg hap.le (sub_nonneg.mpr hl)
    have hi : 0 ≤ (a : ℝ)*(t+(l : ℝ))+b := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) hi]
  · have hm := mul_nonpos_of_nonneg_of_nonpos hap.le (sub_nonpos.mpr hu)
    have hi : (a : ℝ)*(t+(u : ℝ))+b ≤ 0 := by nlinarith
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hu) hi]
  · by_contra hh
    have hm := mul_neg_of_pos_of_neg hap (lt_of_not_ge hh)
    nlinarith [sq_nonneg (2*(a : ℝ)*t+b)]

def SignedSupportCheck (nx ny extent l u e d : ℚ) : Prop :=
  NonnegativeQuadraticCheck (2*extent+e*nx+d*ny)
    (-2*(e*ny-d*nx)) (2*extent-e*nx-d*ny) l u

def SupportExtentCheck (n : QPoint) (extent l u : ℚ) : Prop :=
  SignedSupportCheck n.1 n.2 extent l u 1 1 ∧
  SignedSupportCheck n.1 n.2 extent l u 1 (-1) ∧
  SignedSupportCheck n.1 n.2 extent l u (-1) 1 ∧
  SignedSupportCheck n.1 n.2 extent l u (-1) (-1)

instance supportExtentCheckDecidable (n : QPoint) (extent l u : ℚ) :
    Decidable (SupportExtentCheck n extent l u) := by
  unfold SupportExtentCheck SignedSupportCheck
  infer_instance

theorem signed_support_check_sound (n : QPoint) (extent l u e d : ℚ)
    (hc : SignedSupportCheck n.1 n.2 extent l u e d) (t : ℝ)
    (hl : (l : ℝ) ≤ t) (hu : t ≤ (u : ℝ)) :
    (e : ℝ)*dot (chartAxis t) (realPoint n) +
      (d : ℝ)*dot (perp (chartAxis t)) (realPoint n) ≤ 2*extent := by
  have hp := nonnegative_quadratic_check_sound _ _ _ l u hc t hl hu
  have hd : 0 < 1+t^2 := by positivity
  have he : ((e : ℝ)*dot (chartAxis t) (realPoint n) +
      (d : ℝ)*dot (perp (chartAxis t)) (realPoint n)) * (1+t^2) =
      ((e : ℝ)*n.1+(d : ℝ)*n.2)*(1-t^2)+2*((e : ℝ)*n.2-(d : ℝ)*n.1)*t := by
    dsimp [dot, chartAxis, perp, realPoint]
    field_simp [ne_of_gt hd]
    ring
  apply (mul_le_mul_right hd).mp
  rw [he]
  push_cast at hp
  nlinarith

theorem support_extent_check_sound (n : QPoint) (extent l u : ℚ)
    (hc : SupportExtentCheck n extent l u) (q : UnitSquare) (t : ℝ)
    (hl : (l : ℝ) ≤ t) (hu : t ≤ (u : ℝ)) (ha : q.axis = chartAxis t) :
    projectionRadius q (realPoint n) ≤ extent := by
  have hpp := signed_support_check_sound n extent l u 1 1 hc.1 t hl hu
  have hpm := signed_support_check_sound n extent l u 1 (-1) hc.2.1 t hl hu
  have hmp := signed_support_check_sound n extent l u (-1) 1 hc.2.2.1 t hl hu
  have hmm := signed_support_check_sound n extent l u (-1) (-1) hc.2.2.2 t hl hu
  norm_num only [Rat.cast_one, Rat.cast_neg, one_mul, neg_mul, neg_one_mul] at hpp hpm hmp hmm
  unfold projectionRadius
  rw [ha]
  by_cases hx : 0 ≤ dot (chartAxis t) (realPoint n)
  · rw [abs_of_nonneg hx]
    by_cases hy : 0 ≤ dot (perp (chartAxis t)) (realPoint n)
    · rw [abs_of_nonneg hy]; linarith
    · rw [abs_of_neg (lt_of_not_ge hy)]; linarith
  · rw [abs_of_neg (lt_of_not_ge hx)]
    by_cases hy : 0 ≤ dot (perp (chartAxis t)) (realPoint n)
    · rw [abs_of_nonneg hy]; linarith
    · rw [abs_of_neg (lt_of_not_ge hy)]; linarith

def ownedPointCut (n p : QPoint) (extent : ℚ) : Halfplane :=
  ⟨n.1, n.2, n.1*p.1+n.2*p.2+extent⟩

/-- An actual owned point constrains its square's center. The extent bounds
the actual unit square, never its smaller strict inner core. -/
theorem owned_point_cut_necessary (n p : QPoint) (extent l u : ℚ)
    (hc : SupportExtentCheck n extent l u) (q : UnitSquare)
    (hp : OpenSquare q (realPoint p)) (t : ℝ)
    (hl : (l : ℝ) ≤ t) (hu : t ≤ (u : ℝ)) (ha : q.axis = chartAxis t) :
    (ownedPointCut n p extent).contains q.center := by
  have he := support_extent_check_sound n extent l u hc q t hl hu ha
  have hb := (abs_le.mp ((closed_projection_bound hp.closed (realPoint n)).trans he)).1
  dsimp [ownedPointCut, Halfplane.contains, dot, realPoint] at hb ⊢
  push_cast
  nlinarith

end
end ElevenSquare.Tasks.T01
