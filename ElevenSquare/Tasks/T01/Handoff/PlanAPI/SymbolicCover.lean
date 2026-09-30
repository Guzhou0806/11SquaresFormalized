import ElevenSquare.Tasks.T01.QuarticBernstein
import ElevenSquare.Pending.S06_BaselineCoverCertificate

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A rational quadratic after clearing the uniformly positive chart
denominator `1+t²`. -/
structure SymbolicQuadratic where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  deriving DecidableEq

def SymbolicQuadratic.eval (p : SymbolicQuadratic) (t : ℝ) : ℝ :=
  p.c0 + p.c1*t + p.c2*t^2

def SymbolicQuadratic.quartic (p : SymbolicQuadratic) : Quartic :=
  ⟨p.c0, p.c1, p.c2, 0, 0⟩

def SymbolicQuadratic.neg (p : SymbolicQuadratic) : SymbolicQuadratic :=
  ⟨-p.c0, -p.c1, -p.c2⟩

def SymbolicQuadratic.mul (p q : SymbolicQuadratic) : Quartic :=
  ⟨p.c0*q.c0,
   p.c0*q.c1+p.c1*q.c0,
   p.c0*q.c2+p.c1*q.c1+p.c2*q.c0,
   p.c1*q.c2+p.c2*q.c1,
   p.c2*q.c2⟩

def quarticAdd (p q : Quartic) : Quartic :=
  ⟨p.c0+q.c0,p.c1+q.c1,p.c2+q.c2,p.c3+q.c3,p.c4+q.c4⟩

def quarticSub (p q : Quartic) : Quartic :=
  ⟨p.c0-q.c0,p.c1-q.c1,p.c2-q.c2,p.c3-q.c3,p.c4-q.c4⟩

theorem symbolic_quadratic_quartic_eval (p : SymbolicQuadratic) (t : ℝ) :
    p.quartic.eval t = p.eval t := by
  simp [SymbolicQuadratic.quartic, SymbolicQuadratic.eval, Quartic.eval]

theorem symbolic_quadratic_neg_eval (p : SymbolicQuadratic) (t : ℝ) :
    p.neg.eval t = -p.eval t := by
  dsimp [SymbolicQuadratic.neg, SymbolicQuadratic.eval]
  push_cast
  ring

theorem symbolic_quadratic_mul_eval (p q : SymbolicQuadratic) (t : ℝ) :
    (p.mul q).eval t = p.eval t * q.eval t := by
  dsimp [SymbolicQuadratic.mul, SymbolicQuadratic.eval, Quartic.eval]
  push_cast
  ring

theorem quartic_add_eval (p q : Quartic) (t : ℝ) :
    (quarticAdd p q).eval t = p.eval t + q.eval t := by
  dsimp [quarticAdd, Quartic.eval]
  push_cast
  ring

theorem quartic_sub_eval (p q : Quartic) (t : ℝ) :
    (quarticSub p q).eval t = p.eval t - q.eval t := by
  dsimp [quarticSub, Quartic.eval]
  push_cast
  ring

/-- A halfplane whose three coefficients vary quadratically with angle. -/
structure SymbolicFacet where
  a : SymbolicQuadratic
  b : SymbolicQuadratic
  c : SymbolicQuadratic
  deriving DecidableEq

def SymbolicFacet.contains (f : SymbolicFacet) (t : ℝ) (x : Point) : Prop :=
  f.a.eval t * x.1 + f.b.eval t * x.2 ≤ f.c.eval t

def SymbolicFacet.flip (f : SymbolicFacet) : SymbolicFacet :=
  ⟨f.a.neg, f.b.neg, f.c.neg⟩

def SymbolicPolygonContains (fs : List SymbolicFacet) (t : ℝ) (x : Point) : Prop :=
  ∀ f ∈ fs, f.contains t x

theorem symbolic_facet_flip_contains (f : SymbolicFacet) (t : ℝ) (x : Point)
    (h : ¬ f.contains t x) : f.flip.contains t x := by
  unfold SymbolicFacet.contains at h ⊢
  dsimp [SymbolicFacet.flip]
  rw [symbolic_quadratic_neg_eval, symbolic_quadratic_neg_eval,
    symbolic_quadratic_neg_eval]
  push_neg at h
  linarith

/-- Two-source Farkas implication. The positive denominator and two
nonnegative numerator weights are rational quadratics. Normal identities
are checked as exact quartic coefficient equalities; the cleared slack is a
nonnegative quartic on the entire interval. -/
structure SymbolicFarkasWitness where
  first : ℕ
  second : ℕ
  denominator : SymbolicQuadratic
  firstWeight : SymbolicQuadratic
  secondWeight : SymbolicQuadratic

def SymbolicFarkasWitness.margin (w : SymbolicFarkasWitness)
    (f g target : SymbolicFacet) : Quartic :=
  quarticSub (quarticSub (w.denominator.mul target.c)
    (w.firstWeight.mul f.c)) (w.secondWeight.mul g.c)

def SymbolicFarkasWitness.Check (w : SymbolicFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet) (l u : ℚ) : Prop :=
  w.first < source.length ∧ w.second < source.length ∧
  let f := source.getD w.first ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  let g := source.getD w.second ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  w.denominator.quartic.BernsteinPosCheck l u ∧
  w.firstWeight.quartic.BernsteinNonnegCheck l u ∧
  w.secondWeight.quartic.BernsteinNonnegCheck l u ∧
  quarticAdd (w.firstWeight.mul f.a) (w.secondWeight.mul g.a) =
    w.denominator.mul target.a ∧
  quarticAdd (w.firstWeight.mul f.b) (w.secondWeight.mul g.b) =
    w.denominator.mul target.b ∧
  (w.margin f g target).BernsteinNonnegCheck l u

instance symbolicFarkasCheckDecidable (w : SymbolicFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet) (l u : ℚ) :
    Decidable (w.Check source target l u) := by
  unfold SymbolicFarkasWitness.Check
  infer_instance

theorem symbolic_farkas_sound (w : SymbolicFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet) (l u : ℚ)
    (hc : w.Check source target l u) (t : ℝ)
    (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ)) (x : Point)
    (hx : SymbolicPolygonContains source t x) : target.contains t x := by
  let z : SymbolicFacet := ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  let f := source.getD w.first z
  let g := source.getD w.second z
  have hf : f.contains t x := hx f (by
    dsimp [f]
    rw [List.getD_eq_get source z hc.1]
    exact List.get_mem ..)
  have hg : g.contains t x := hx g (by
    dsimp [g]
    rw [List.getD_eq_get source z hc.2.1]
    exact List.get_mem ..)
  have hd : 0 < w.denominator.eval t := by
    have h := quartic_bernstein_pos _ l u hc.2.2.1 t hlt htu
    simpa only [symbolic_quadratic_quartic_eval] using h
  have hw₁ : 0 ≤ w.firstWeight.eval t := by
    have h := quartic_bernstein_nonneg _ l u hc.2.2.2.1 t hlt htu
    simpa only [symbolic_quadratic_quartic_eval] using h
  have hw₂ : 0 ≤ w.secondWeight.eval t := by
    have h := quartic_bernstein_nonneg _ l u hc.2.2.2.2.1 t hlt htu
    simpa only [symbolic_quadratic_quartic_eval] using h
  have ha : w.firstWeight.eval t * f.a.eval t +
      w.secondWeight.eval t * g.a.eval t =
      w.denominator.eval t * target.a.eval t := by
    have h := congrArg (fun q : Quartic => q.eval t) hc.2.2.2.2.2.1
    simpa only [quartic_add_eval, symbolic_quadratic_mul_eval] using h
  have hb : w.firstWeight.eval t * f.b.eval t +
      w.secondWeight.eval t * g.b.eval t =
      w.denominator.eval t * target.b.eval t := by
    have h := congrArg (fun q : Quartic => q.eval t) hc.2.2.2.2.2.2.1
    simpa only [quartic_add_eval, symbolic_quadratic_mul_eval] using h
  have hm : w.firstWeight.eval t * f.c.eval t +
      w.secondWeight.eval t * g.c.eval t ≤
      w.denominator.eval t * target.c.eval t := by
    have h := quartic_bernstein_nonneg _ l u hc.2.2.2.2.2.2.2 t hlt htu
    dsimp [SymbolicFarkasWitness.margin] at h
    simp only [quartic_sub_eval, symbolic_quadratic_mul_eval] at h
    linarith
  unfold SymbolicFacet.contains at hf hg ⊢
  have h₁ := mul_le_mul_of_nonneg_left hf hw₁
  have h₂ := mul_le_mul_of_nonneg_left hg hw₂
  have hscaled : w.denominator.eval t *
      (target.a.eval t * x.1 + target.b.eval t * x.2) ≤
      w.denominator.eval t * target.c.eval t := by
    calc
      w.denominator.eval t *
          (target.a.eval t * x.1 + target.b.eval t * x.2) =
        (w.denominator.eval t * target.a.eval t) * x.1 +
        (w.denominator.eval t * target.b.eval t) * x.2 := by ring
      _ = (w.firstWeight.eval t * f.a.eval t +
          w.secondWeight.eval t * g.a.eval t) * x.1 +
        (w.firstWeight.eval t * f.b.eval t +
          w.secondWeight.eval t * g.b.eval t) * x.2 := by
            rw [ha, hb]
      _ = w.firstWeight.eval t * (f.a.eval t * x.1 + f.b.eval t * x.2) +
          w.secondWeight.eval t * (g.a.eval t * x.1 + g.b.eval t * x.2) := by ring
      _ ≤ w.firstWeight.eval t * f.c.eval t +
          w.secondWeight.eval t * g.c.eval t := add_le_add h₁ h₂
      _ ≤ w.denominator.eval t * target.c.eval t := hm
  exact (mul_le_mul_left hd).mp hscaled

/-- Exact coefficient identities and interval signs for every target facet. -/
def SymbolicPolygonImplicationCheck (source target : List SymbolicFacet)
    (ws : List SymbolicFarkasWitness) (l u : ℚ) : Prop :=
  target.length = ws.length ∧
    ∀ fw ∈ target.zip ws, fw.2.Check source fw.1 l u

instance symbolicPolygonImplicationCheckDecidable
    (source target : List SymbolicFacet) (ws : List SymbolicFarkasWitness)
    (l u : ℚ) : Decidable (SymbolicPolygonImplicationCheck source target ws l u) := by
  unfold SymbolicPolygonImplicationCheck
  infer_instance

theorem symbolic_polygon_implication_sound (source target : List SymbolicFacet)
    (ws : List SymbolicFarkasWitness) (l u : ℚ)
    (hc : SymbolicPolygonImplicationCheck source target ws l u)
    (t : ℝ) (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ)) (x : Point)
    (hx : SymbolicPolygonContains source t x) :
    SymbolicPolygonContains target t x := by
  intro desired hdesired
  have hgo : ∀ (fs : List SymbolicFacet) (vs : List SymbolicFarkasWitness),
      fs.length = vs.length →
      (∀ fw ∈ fs.zip vs, fw.2.Check source fw.1 l u) →
      ∀ f ∈ fs, f.contains t x := by
    intro fs
    induction fs with
    | nil => intro vs _ _ f hf; simp at hf
    | cons head tail ih =>
      intro vs hlen hcheck targetFacet hmem
      cases vs with
      | nil => simp at hlen
      | cons w vs =>
        rcases List.mem_cons.mp hmem with hhead | htail
        · subst targetFacet
          have hw : w.Check source head l u := hcheck (head,w) (by simp)
          exact symbolic_farkas_sound w source head l u hw t hlt htu x hx
        · exact ih vs (by simpa using hlen)
            (fun fw hfw => hcheck fw (by simp [hfw])) targetFacet htail
  exact hgo target ws hc.1 hc.2 desired hdesired

/-- A moving halfplane BSP. The split is closed on both sides, so a point
on a moving boundary cannot fall through the cover. -/
inductive SymbolicCoverCertificate where
  | hit (index : ℕ) (witnesses : List SymbolicFarkasWitness)
  | split (facet : SymbolicFacet)
      (left right : SymbolicCoverCertificate)

def SymbolicCoverCertificate.Check (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (l u : ℚ) :
    SymbolicCoverCertificate → Prop
  | .hit i ws => i < targets.length ∧
      SymbolicPolygonImplicationCheck source (targets.getD i []) ws l u
  | .split facet left right =>
      left.Check (facet :: source) targets l u ∧
        right.Check (facet.flip :: source) targets l u

instance symbolicCoverCheckDecidable (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (l u : ℚ)
    (c : SymbolicCoverCertificate) : Decidable (c.Check source targets l u) := by
  induction c generalizing source with
  | hit i ws =>
    change Decidable (i < targets.length ∧
      SymbolicPolygonImplicationCheck source (targets.getD i []) ws l u)
    infer_instance
  | split facet left right ihl ihr =>
    letI := ihl (facet :: source)
    letI := ihr (facet.flip :: source)
    change Decidable (left.Check (facet :: source) targets l u ∧
      right.Check (facet.flip :: source) targets l u)
    infer_instance

theorem symbolic_cover_sound (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (l u : ℚ)
    (c : SymbolicCoverCertificate) (hc : c.Check source targets l u)
    (t : ℝ) (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ)) (x : Point)
    (hx : SymbolicPolygonContains source t x) :
    ∃ target ∈ targets, SymbolicPolygonContains target t x := by
  induction c generalizing source with
  | hit i ws =>
    refine ⟨targets.getD i [], ?_,
      symbolic_polygon_implication_sound source (targets.getD i []) ws l u
        hc.2 t hlt htu x hx⟩
    rw [List.getD_eq_get targets [] hc.1]
    exact List.get_mem ..
  | split facet left right ihl ihr =>
    by_cases hfacet : facet.contains t x
    · apply ihl (facet :: source) hc.1
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hfacet
      · exact hx f hf
    · apply ihr (facet.flip :: source) hc.2
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact symbolic_facet_flip_contains facet t x hfacet
      · exact hx f hf

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_cover_sound
