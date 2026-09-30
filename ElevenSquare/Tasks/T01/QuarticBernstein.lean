import ElevenSquare.Tasks.T01.Quadratic

namespace ElevenSquare.Tasks.T01
noncomputable section

/-- A degree-at-most-four polynomial with exact rational power coefficients. -/
structure Quartic where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  c4 : ℚ
  deriving DecidableEq

def Quartic.eval (p : Quartic) (t : ℝ) : ℝ :=
  p.c0 + p.c1*t + p.c2*t^2 + p.c3*t^3 + p.c4*t^4

def Quartic.shift (p : Quartic) (l u : ℚ) : Quartic :=
  let w := u-l
  { c0 := p.c0 + p.c1*l + p.c2*l^2 + p.c3*l^3 + p.c4*l^4
    c1 := w*(p.c1 + 2*p.c2*l + 3*p.c3*l^2 + 4*p.c4*l^3)
    c2 := w^2*(p.c2 + 3*p.c3*l + 6*p.c4*l^2)
    c3 := w^3*(p.c3 + 4*p.c4*l)
    c4 := w^4*p.c4 }

def Quartic.toBernstein (p : Quartic) : Quartic :=
  { c0 := p.c0
    c1 := p.c0 + p.c1/4
    c2 := p.c0 + p.c1/2 + p.c2/6
    c3 := p.c0 + 3*p.c1/4 + p.c2/2 + p.c3/4
    c4 := p.c0 + p.c1 + p.c2 + p.c3 + p.c4 }

/-- Five exact Bernstein coefficients of `p` on `[l,u]`. -/
def Quartic.bernsteinOn (p : Quartic) (l u : ℚ) : Quartic :=
  (p.shift l u).toBernstein

private def Quartic.bernsteinExpr (b : Quartic) (s : ℝ) : ℝ :=
  b.c0*(1-s)^4 + 4*b.c1*s*(1-s)^3 + 6*b.c2*s^2*(1-s)^2 +
    4*b.c3*s^3*(1-s) + b.c4*s^4

private theorem quartic_bernstein_identity (p : Quartic) (l u : ℚ) (s : ℝ) :
    p.eval ((l:ℝ) + ((u-l:ℚ):ℝ)*s) =
      (p.bernsteinOn l u).bernsteinExpr s := by
  unfold Quartic.eval Quartic.bernsteinOn Quartic.shift
    Quartic.toBernstein Quartic.bernsteinExpr
  push_cast
  ring

def Quartic.BernsteinNonnegCheck (p : Quartic) (l u : ℚ) : Prop :=
  l < u ∧
    let b := p.bernsteinOn l u
    0 ≤ b.c0 ∧ 0 ≤ b.c1 ∧ 0 ≤ b.c2 ∧ 0 ≤ b.c3 ∧ 0 ≤ b.c4

def Quartic.BernsteinPosCheck (p : Quartic) (l u : ℚ) : Prop :=
  l < u ∧
    let b := p.bernsteinOn l u
    0 < b.c0 ∧ 0 < b.c1 ∧ 0 < b.c2 ∧ 0 < b.c3 ∧ 0 < b.c4

instance (p : Quartic) (l u : ℚ) : Decidable (p.BernsteinNonnegCheck l u) := by
  unfold Quartic.BernsteinNonnegCheck
  infer_instance

instance (p : Quartic) (l u : ℚ) : Decidable (p.BernsteinPosCheck l u) := by
  unfold Quartic.BernsteinPosCheck
  infer_instance

private theorem bernstein_expr_nonneg (b : Quartic) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hb : 0 ≤ (b.c0:ℝ) ∧ 0 ≤ (b.c1:ℝ) ∧ 0 ≤ (b.c2:ℝ) ∧
      0 ≤ (b.c3:ℝ) ∧ 0 ≤ (b.c4:ℝ)) :
    0 ≤ b.bernsteinExpr s := by
  have hsub : 0 ≤ 1-s := by linarith
  rcases hb with ⟨h0, h1, h2, h3, h4⟩
  unfold Quartic.bernsteinExpr
  positivity

private theorem bernstein_expr_pos (b : Quartic) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hb : 0 < (b.c0:ℝ) ∧ 0 < (b.c1:ℝ) ∧ 0 < (b.c2:ℝ) ∧
      0 < (b.c3:ℝ) ∧ 0 < (b.c4:ℝ)) :
    0 < b.bernsteinExpr s := by
  have hsub : 0 ≤ 1-s := by linarith
  rcases hb with ⟨h0, h1, h2, h3, h4⟩
  by_cases he : s = 1
  · subst s
    simpa [Quartic.bernsteinExpr] using h4
  · have hlt : s < 1 := lt_of_le_of_ne hs1 he
    have hfirst : 0 < (b.c0:ℝ)*(1-s)^4 :=
      mul_pos h0 (pow_pos (sub_pos.mpr hlt) _)
    have hterm1 : 0 ≤ 4*(b.c1:ℝ)*s*(1-s)^3 := by positivity
    have hterm2 : 0 ≤ 6*(b.c2:ℝ)*s^2*(1-s)^2 := by positivity
    have hterm3 : 0 ≤ 4*(b.c3:ℝ)*s^3*(1-s) := by positivity
    have hterm4 : 0 ≤ (b.c4:ℝ)*s^4 := by positivity
    unfold Quartic.bernsteinExpr
    linarith

private theorem quartic_interval_parameter (l u : ℚ) (t : ℝ)
    (hlu : l < u) (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ)) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      t = (l:ℝ) + ((u-l:ℚ):ℝ)*s := by
  have hw : 0 < (u:ℝ)-(l:ℝ) := by exact_mod_cast sub_pos.mpr hlu
  let s := (t-(l:ℝ))/((u:ℝ)-(l:ℝ))
  refine ⟨s, ?_, ?_, ?_⟩
  · exact div_nonneg (sub_nonneg.mpr hlt) hw.le
  · apply (div_le_one hw).mpr
    linarith
  · dsimp [s]
    push_cast
    field_simp [ne_of_gt hw] <;> ring

/-- A five-coefficient rational check proves nonnegativity everywhere on an
interval, including both endpoints. -/
theorem quartic_bernstein_nonneg (p : Quartic) (l u : ℚ)
    (hc : p.BernsteinNonnegCheck l u) (t : ℝ)
    (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ)) : 0 ≤ p.eval t := by
  obtain ⟨s, hs0, hs1, rfl⟩ :=
    quartic_interval_parameter l u t hc.1 hlt htu
  rw [quartic_bernstein_identity]
  apply bernstein_expr_nonneg _ s hs0 hs1
  dsimp [Quartic.BernsteinNonnegCheck] at hc
  rcases hc.2 with ⟨h0,h1,h2,h3,h4⟩
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1,
    by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4⟩

/-- A five-coefficient rational check proves strict positivity everywhere
on an interval, including both endpoints. -/
theorem quartic_bernstein_pos (p : Quartic) (l u : ℚ)
    (hc : p.BernsteinPosCheck l u) (t : ℝ)
    (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ)) : 0 < p.eval t := by
  obtain ⟨s, hs0, hs1, rfl⟩ :=
    quartic_interval_parameter l u t hc.1 hlt htu
  rw [quartic_bernstein_identity]
  apply bernstein_expr_pos _ s hs0 hs1
  dsimp [Quartic.BernsteinPosCheck] at hc
  rcases hc.2 with ⟨h0,h1,h2,h3,h4⟩
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1,
    by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4⟩

/-- An exact rational partition of an interval. The same polynomial is
checked on each leaf, so dyadic refinement costs only five sign tests per
leaf and never changes the underlying geometric regime. -/
inductive QuarticIntervalCertificate where
  | leaf
  | split (mid : ℚ) (left right : QuarticIntervalCertificate)

def QuarticIntervalCertificate.Check (strict : Bool) (p : Quartic)
    (l u : ℚ) : QuarticIntervalCertificate → Prop
  | .leaf => if strict then p.BernsteinPosCheck l u
      else p.BernsteinNonnegCheck l u
  | .split mid left right =>
      l < mid ∧ mid < u ∧
        left.Check strict p l mid ∧ right.Check strict p mid u

instance quarticIntervalCertificateCheckDecidable (strict : Bool) (p : Quartic) (l u : ℚ)
    (c : QuarticIntervalCertificate) : Decidable (c.Check strict p l u) := by
  induction c generalizing l u with
  | leaf =>
    cases strict
    · change Decidable (p.BernsteinNonnegCheck l u)
      infer_instance
    · change Decidable (p.BernsteinPosCheck l u)
      infer_instance
  | split mid left right ihl ihr =>
    letI := ihl l mid
    letI := ihr mid u
    change Decidable (l < mid ∧ mid < u ∧
      left.Check strict p l mid ∧ right.Check strict p mid u)
    infer_instance

def QuarticIntervalCertificate.leafCount : QuarticIntervalCertificate → ℕ
  | .leaf => 1
  | .split _ left right => left.leafCount + right.leafCount

theorem quartic_interval_certificate_sound (strict : Bool) (p : Quartic)
    (l u : ℚ) (c : QuarticIntervalCertificate)
    (hc : c.Check strict p l u) (t : ℝ)
    (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ)) :
    if strict then 0 < p.eval t else 0 ≤ p.eval t := by
  induction c generalizing l u with
  | leaf =>
    cases strict with
    | false => exact quartic_bernstein_nonneg p l u hc t hlt htu
    | true => exact quartic_bernstein_pos p l u hc t hlt htu
  | split mid left right ihl ihr =>
    rcases hc with ⟨_, _, hleft, hright⟩
    by_cases ht : t ≤ (mid:ℝ)
    · exact ihl l mid hleft hlt ht
    · have hmt : (mid:ℝ) ≤ t := le_of_lt (lt_of_not_ge ht)
      exact ihr mid u hright hmt htu

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.quartic_bernstein_nonneg
#print axioms ElevenSquare.Tasks.T01.quartic_bernstein_pos
#print axioms ElevenSquare.Tasks.T01.quartic_interval_certificate_sound
