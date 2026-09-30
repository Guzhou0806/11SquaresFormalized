import ElevenSquare.Tasks.T01.SymbolicWall
import ElevenSquare.Tasks.T01.QuarticBernstein

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- Exact coefficients for the quadratic dual weights. -/
structure WallQuadratic where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  deriving DecidableEq

def WallQuadratic.eval (p : WallQuadratic) (t : ℝ) : ℝ :=
  p.c0 + p.c1*t + p.c2*t^2

def WallQuadratic.quartic (p : WallQuadratic) : Quartic :=
  ⟨p.c0, p.c1, p.c2, 0, 0⟩

def WallQuadratic.linear (p q : WallQuadratic) (a b : ℚ) : WallQuadratic :=
  ⟨a*p.c0+b*q.c0, a*p.c1+b*q.c1, a*p.c2+b*q.c2⟩

def wallDirectionPolynomials : Fin 4 → WallQuadratic × WallQuadratic :=
  ![(⟨1,0,-1⟩, ⟨0,2,0⟩), (⟨-1,0,1⟩, ⟨0,-2,0⟩),
    (⟨0,-2,0⟩, ⟨1,0,-1⟩), (⟨0,2,0⟩, ⟨-1,0,1⟩)]

theorem wall_direction_polynomials_eval (k : Fin 4) (t : ℝ) :
    ((wallDirectionPolynomials k).1.eval t, (wallDirectionPolynomials k).2.eval t) =
      chartDirectionNumerator t k := by
  fin_cases k <;> simp [wallDirectionPolynomials, WallQuadratic.eval,
    chartDirectionNumerator] <;> ring

def wallDualFirstPolynomial (f g : SymbolicWallFacet) (k : Fin 4) : WallQuadratic :=
  (wallDirectionPolynomials k).1.linear (wallDirectionPolynomials k).2
    (g.b / f.determinant g) (-g.a / f.determinant g)

def wallDualSecondPolynomial (f g : SymbolicWallFacet) (k : Fin 4) : WallQuadratic :=
  (wallDirectionPolynomials k).1.linear (wallDirectionPolynomials k).2
    (-f.b / f.determinant g) (f.a / f.determinant g)

theorem wall_dual_polynomials_eval (f g : SymbolicWallFacet) (k : Fin 4) (t : ℝ) :
    (wallDualFirstPolynomial f g k).eval t =
      f.dualFirst g (chartDirectionNumerator t k) ∧
    (wallDualSecondPolynomial f g k).eval t =
      f.dualSecond g (chartDirectionNumerator t k) := by
  have hx := congrArg Prod.fst (wall_direction_polynomials_eval k t)
  have hy := congrArg Prod.snd (wall_direction_polynomials_eval k t)
  dsimp only at hx hy
  unfold SymbolicWallFacet.dualFirst SymbolicWallFacet.dualSecond
  rw [← hx, ← hy]
  constructor
  all_goals
    dsimp [wallDualFirstPolynomial, wallDualSecondPolynomial,
      WallQuadratic.linear, WallQuadratic.eval]
    push_cast
    ring

/-- Clearing the strictly positive denominator of the exact wall bound gives
one quartic, rather than separate angle-bin ownership checks. -/
def wallDualMargin (f g : SymbolicWallFacet) (k : Fin 4) (p : QPoint) : Quartic :=
  let u := wallDualFirstPolynomial f g k
  let v := wallDualSecondPolynomial f g k
  let a := (wallDirectionPolynomials k).1.linear (wallDirectionPolynomials k).2 p.1 p.2
  let r := a.linear (u.linear v f.c g.c) 1 (-1)
  let s := u.linear v f.d g.d
  ⟨2*r.c0+1-s.c0,
    2*r.c1-2*s.c0-s.c1,
    2*r.c2+2*r.c0+2+s.c0-2*s.c1-s.c2,
    2*r.c1+s.c1-2*s.c2,
    2*r.c2+1+s.c2⟩

theorem wall_dual_margin_eval (f g : SymbolicWallFacet) (k : Fin 4)
    (p : QPoint) (t : ℝ) :
    (wallDualMargin f g k p).eval t =
      2*(1+t^2) * (dot (chartDirectionNumerator t k) (realPoint p) + (1+t^2)/2 -
        (wallDualFirstPolynomial f g k).eval t * f.bound t -
        (wallDualSecondPolynomial f g k).eval t * g.bound t) := by
  have hd : 1+t^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1+t^2)
  have hx := congrArg Prod.fst (wall_direction_polynomials_eval k t)
  have hy := congrArg Prod.snd (wall_direction_polynomials_eval k t)
  dsimp only at hx hy
  simp only [dot]
  rw [← hx, ← hy]
  unfold wallDualMargin Quartic.eval SymbolicWallFacet.bound
  rw [exactWallMargin_formula]
  dsimp [WallQuadratic.linear, WallQuadratic.eval, dot, realPoint]
  push_cast
  field_simp [hd]
  <;> ring

/-- A single interval certificate for one supporting pair and one owned point.
The exact weights and margin are computed from the facets and point. -/
def WallDualCheck (f g : SymbolicWallFacet) (k : Fin 4)
    (p : QPoint) (l u : ℚ) : Prop :=
  f.determinant g ≠ 0 ∧
    (wallDualFirstPolynomial f g k).quartic.BernsteinNonnegCheck l u ∧
    (wallDualSecondPolynomial f g k).quartic.BernsteinNonnegCheck l u ∧
    (wallDualMargin f g k p).BernsteinPosCheck l u

instance (f g : SymbolicWallFacet) (k : Fin 4) (p : QPoint) (l u : ℚ) :
    Decidable (WallDualCheck f g k p l u) := by
  unfold WallDualCheck
  infer_instance

/-- The semantic two-facet certificate, shared by ordinary and crossing intervals. -/
def WallDualSupports (f g : SymbolicWallFacet) (k : Fin 4) (p : QPoint) (t : ℝ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
    a*f.a+b*g.a = (chartDirectionNumerator t k).1 ∧
    a*f.b+b*g.b = (chartDirectionNumerator t k).2 ∧
    a*f.bound t+b*g.bound t < dot (chartDirectionNumerator t k) (realPoint p)+(1+t^2)/2

theorem wall_dual_polynomial_supports (f g : SymbolicWallFacet) (k : Fin 4)
    (p : QPoint) (t : ℝ) (hdet : f.determinant g ≠ 0)
    (hu : 0 ≤ (wallDualFirstPolynomial f g k).eval t)
    (hv : 0 ≤ (wallDualSecondPolynomial f g k).eval t)
    (hm : 0 < (wallDualMargin f g k p).eval t) : WallDualSupports f g k p t := by
  have he := wall_dual_polynomials_eval f g k t
  have hn := symbolic_wall_dual_normals f g (chartDirectionNumerator t k) hdet
  refine ⟨(wallDualFirstPolynomial f g k).eval t,
    (wallDualSecondPolynomial f g k).eval t, hu, hv, ?_, ?_, ?_⟩
  · rw [he.1, he.2]; exact hn.1
  · rw [he.1, he.2]; exact hn.2
  · rw [wall_dual_margin_eval] at hm
    have hd : 0 < 2*(1+t^2) := by positivity
    have hp := (mul_pos_iff_of_pos_left hd).mp hm
    linarith only [hp]

theorem wall_quadratic_bernstein_nonneg (p : WallQuadratic) (l u : ℚ)
    (hc : p.quartic.BernsteinNonnegCheck l u) (t : ℝ)
    (hl : (l:ℝ) ≤ t) (hu : t ≤ (u:ℝ)) : 0 ≤ p.eval t := by
  have h := quartic_bernstein_nonneg _ l u hc t hl hu
  simpa only [WallQuadratic.quartic, Quartic.eval, Rat.cast_zero, zero_mul,
    add_zero, WallQuadratic.eval] using h

theorem wall_dual_check_sound (f g : SymbolicWallFacet) (k : Fin 4)
    (p : QPoint) (l u : ℚ) (hc : WallDualCheck f g k p l u)
    (t : ℝ) (hl : (l:ℝ) ≤ t) (hu : t ≤ (u:ℝ)) : WallDualSupports f g k p t := by
  obtain ⟨hdet, hfirst, hsecond, hmargin⟩ := hc
  exact wall_dual_polynomial_supports f g k p t hdet
    (wall_quadratic_bernstein_nonneg _ l u hfirst t hl hu)
    (wall_quadratic_bernstein_nonneg _ l u hsecond t hl hu)
    (quartic_bernstein_pos _ l u hmargin t hl hu)

def WallQuadratic.negScale (p : WallQuadratic) (r : ℚ) : WallQuadratic :=
  ⟨-r*p.c0, -r*p.c1, -r*p.c2⟩

/-- Two adjacent supporting pairs straddle a possibly irrational angle.
A polynomial sign split chooses a valid pair, so rational endpoints suffice. -/
def WallDualCrossingCheck (f g h : SymbolicWallFacet) (k : Fin 4)
    (p : QPoint) (l u r : ℚ) : Prop :=
  f.determinant g ≠ 0 ∧ g.determinant h ≠ 0 ∧ 0 < r ∧
    wallDualSecondPolynomial g h k = (wallDualFirstPolynomial f g k).negScale r ∧
    (wallDualSecondPolynomial f g k).quartic.BernsteinNonnegCheck l u ∧
    (wallDualFirstPolynomial g h k).quartic.BernsteinNonnegCheck l u ∧
    (wallDualMargin f g k p).BernsteinPosCheck l u ∧
    (wallDualMargin g h k p).BernsteinPosCheck l u

instance (f g h : SymbolicWallFacet) (k : Fin 4) (p : QPoint) (l u r : ℚ) :
    Decidable (WallDualCrossingCheck f g h k p l u r) := by
  unfold WallDualCrossingCheck
  infer_instance

theorem wall_dual_crossing_check_sound (f g h : SymbolicWallFacet) (k : Fin 4)
    (p : QPoint) (l u r : ℚ) (hc : WallDualCrossingCheck f g h k p l u r)
    (t : ℝ) (hl : (l:ℝ) ≤ t) (hu : t ≤ (u:ℝ)) :
    WallDualSupports f g k p t ∨ WallDualSupports g h k p t := by
  obtain ⟨hfg, hgh, hr, he, hleft, hright, hml, hmr⟩ := hc
  by_cases hs : 0 ≤ (wallDualFirstPolynomial f g k).eval t
  · exact Or.inl (wall_dual_polynomial_supports f g k p t hfg hs
      (wall_quadratic_bernstein_nonneg _ l u hleft t hl hu)
      (quartic_bernstein_pos _ l u hml t hl hu))
  · apply Or.inr
    apply wall_dual_polynomial_supports g h k p t hgh
      (wall_quadratic_bernstein_nonneg _ l u hright t hl hu) _
      (quartic_bernstein_pos _ l u hmr t hl hu)
    have hev : (wallDualSecondPolynomial g h k).eval t =
        -(r:ℝ)*(wallDualFirstPolynomial f g k).eval t := by
      rw [he]
      dsimp [WallQuadratic.negScale, WallQuadratic.eval]
      push_cast
      ring
    rw [hev]
    have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hr'.le) (le_of_not_ge hs)

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.wall_dual_check_sound
#print axioms ElevenSquare.Tasks.T01.wall_dual_crossing_check_sound
