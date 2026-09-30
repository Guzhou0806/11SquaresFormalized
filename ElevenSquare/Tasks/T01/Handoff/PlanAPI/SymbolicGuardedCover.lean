import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCover

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A nonnegative quartic may be checked directly or by an exact factorization
through a quadratic angle guard. The factor certificate proves positivity on
the full rational interval, while the guard may switch sign at an irrational
angle inside that interval. -/
inductive GuardedSignCertificate where
  | plain
  | factor (quotient : SymbolicQuadratic)

def GuardedSignCertificate.Check (c : GuardedSignCertificate)
    (guard : SymbolicQuadratic) (p : Quartic) (l u : ℚ) : Prop :=
  match c with
  | .plain => p.BernsteinNonnegCheck l u
  | .factor q => p = guard.mul q ∧ q.quartic.BernsteinNonnegCheck l u

instance guardedSignCheckDecidable (c : GuardedSignCertificate)
    (guard : SymbolicQuadratic) (p : Quartic) (l u : ℚ) :
    Decidable (c.Check guard p l u) := by
  cases c <;> dsimp [GuardedSignCertificate.Check] <;> infer_instance

theorem guarded_sign_sound (c : GuardedSignCertificate)
    (guard : SymbolicQuadratic) (p : Quartic) (l u : ℚ)
    (hc : c.Check guard p l u) (t : ℝ)
    (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
    (hguard : 0 ≤ guard.eval t) : 0 ≤ p.eval t := by
  cases c with
  | plain => exact quartic_bernstein_nonneg p l u hc t hlt htu
  | factor quotient =>
      rw [hc.1, symbolic_quadratic_mul_eval]
      exact mul_nonneg hguard
        (by
          have h := quartic_bernstein_nonneg _ l u hc.2 t hlt htu
          simpa only [symbolic_quadratic_quartic_eval] using h)

/-- A two-facet Farkas witness with three guarded sign proofs. The normal
identities and positive denominator remain unconditional exact checks. -/
structure GuardedFarkasWitness where
  farkas : SymbolicFarkasWitness
  firstSign : GuardedSignCertificate
  secondSign : GuardedSignCertificate
  marginSign : GuardedSignCertificate

def GuardedFarkasWitness.Check (v : GuardedFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet)
    (guard : SymbolicQuadratic) (l u : ℚ) : Prop :=
  let w := v.farkas
  w.first < source.length ∧ w.second < source.length ∧
  let f := source.getD w.first ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  let g := source.getD w.second ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  w.denominator.quartic.BernsteinPosCheck l u ∧
  v.firstSign.Check guard w.firstWeight.quartic l u ∧
  v.secondSign.Check guard w.secondWeight.quartic l u ∧
  quarticAdd (w.firstWeight.mul f.a) (w.secondWeight.mul g.a) =
    w.denominator.mul target.a ∧
  quarticAdd (w.firstWeight.mul f.b) (w.secondWeight.mul g.b) =
    w.denominator.mul target.b ∧
  v.marginSign.Check guard (w.margin f g target) l u

instance guardedFarkasCheckDecidable (v : GuardedFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet)
    (guard : SymbolicQuadratic) (l u : ℚ) :
    Decidable (v.Check source target guard l u) := by
  unfold GuardedFarkasWitness.Check
  infer_instance

theorem symbolic_farkas_pointwise (w : SymbolicFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet)
    (hfirst : w.first < source.length) (hsecond : w.second < source.length)
    (ha : quarticAdd (w.firstWeight.mul
        (source.getD w.first ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩).a)
        (w.secondWeight.mul
        (source.getD w.second ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩).a) =
      w.denominator.mul target.a)
    (hb : quarticAdd (w.firstWeight.mul
        (source.getD w.first ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩).b)
        (w.secondWeight.mul
        (source.getD w.second ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩).b) =
      w.denominator.mul target.b)
    (t : ℝ) (x : Point)
    (hx : SymbolicPolygonContains source t x)
    (hd : 0 < w.denominator.eval t)
    (hw₁ : 0 ≤ w.firstWeight.eval t)
    (hw₂ : 0 ≤ w.secondWeight.eval t)
    (hm : 0 ≤ (w.margin
      (source.getD w.first ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩)
      (source.getD w.second ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩)
      target).eval t) :
    target.contains t x := by
  let z : SymbolicFacet := ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  let f := source.getD w.first z
  let g := source.getD w.second z
  have hf : f.contains t x := hx f (by
    dsimp [f]
    rw [List.getD_eq_getElem source z hfirst]
    exact List.get_mem ..)
  have hg : g.contains t x := hx g (by
    dsimp [g]
    rw [List.getD_eq_getElem source z hsecond]
    exact List.get_mem ..)
  have hna : w.firstWeight.eval t * f.a.eval t +
      w.secondWeight.eval t * g.a.eval t =
      w.denominator.eval t * target.a.eval t := by
    have h := congrArg (fun q : Quartic => q.eval t) ha
    simpa only [quartic_add_eval, symbolic_quadratic_mul_eval] using h
  have hnb : w.firstWeight.eval t * f.b.eval t +
      w.secondWeight.eval t * g.b.eval t =
      w.denominator.eval t * target.b.eval t := by
    have h := congrArg (fun q : Quartic => q.eval t) hb
    simpa only [quartic_add_eval, symbolic_quadratic_mul_eval] using h
  have hmargin : w.firstWeight.eval t * f.c.eval t +
      w.secondWeight.eval t * g.c.eval t ≤
      w.denominator.eval t * target.c.eval t := by
    dsimp [SymbolicFarkasWitness.margin] at hm
    simp only [quartic_sub_eval, symbolic_quadratic_mul_eval] at hm
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
          w.secondWeight.eval t * g.b.eval t) * x.2 := by rw [hna, hnb]
      _ = w.firstWeight.eval t * (f.a.eval t * x.1 + f.b.eval t * x.2) +
          w.secondWeight.eval t * (g.a.eval t * x.1 + g.b.eval t * x.2) := by ring
      _ ≤ w.firstWeight.eval t * f.c.eval t +
          w.secondWeight.eval t * g.c.eval t := add_le_add h₁ h₂
      _ ≤ w.denominator.eval t * target.c.eval t := hmargin
  exact (mul_le_mul_iff_of_pos_left hd).mp hscaled

theorem guarded_farkas_sound (v : GuardedFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet)
    (guard : SymbolicQuadratic) (l u : ℚ)
    (hc : v.Check source target guard l u)
    (t : ℝ) (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
    (hguard : 0 ≤ guard.eval t) (x : Point)
    (hx : SymbolicPolygonContains source t x) : target.contains t x := by
  let w := v.farkas
  let z : SymbolicFacet := ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  let f := source.getD w.first z
  let g := source.getD w.second z
  rcases hc with ⟨hfirst, hsecond, hden, hweight1, hweight2,
    hnormalA, hnormalB, hmargin⟩
  apply symbolic_farkas_pointwise w source target hfirst hsecond
    hnormalA hnormalB t x hx
  · have hp := quartic_bernstein_pos _ l u hden t hlt htu
    simpa only [symbolic_quadratic_quartic_eval] using hp
  · have hp := guarded_sign_sound v.firstSign guard w.firstWeight.quartic
      l u hweight1 t hlt htu hguard
    simpa only [symbolic_quadratic_quartic_eval] using hp
  · have hp := guarded_sign_sound v.secondSign guard w.secondWeight.quartic
      l u hweight2 t hlt htu hguard
    simpa only [symbolic_quadratic_quartic_eval] using hp
  · exact guarded_sign_sound v.marginSign guard (w.margin f g target)
      l u hmargin t hlt htu hguard

def GuardedPolygonImplicationCheck (source target : List SymbolicFacet)
    (ws : List GuardedFarkasWitness) (guard : SymbolicQuadratic)
    (l u : ℚ) : Prop :=
  target.length = ws.length ∧
    ∀ fw ∈ target.zip ws, fw.2.Check source fw.1 guard l u

instance guardedPolygonImplicationCheckDecidable
    (source target : List SymbolicFacet) (ws : List GuardedFarkasWitness)
    (guard : SymbolicQuadratic) (l u : ℚ) :
    Decidable (GuardedPolygonImplicationCheck source target ws guard l u) := by
  unfold GuardedPolygonImplicationCheck
  infer_instance

theorem guarded_polygon_implication_sound (source target : List SymbolicFacet)
    (ws : List GuardedFarkasWitness) (guard : SymbolicQuadratic)
    (l u : ℚ) (hc : GuardedPolygonImplicationCheck source target ws guard l u)
    (t : ℝ) (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
    (hguard : 0 ≤ guard.eval t) (x : Point)
    (hx : SymbolicPolygonContains source t x) :
    SymbolicPolygonContains target t x := by
  intro desired hdesired
  have hgo : ∀ (fs : List SymbolicFacet) (vs : List GuardedFarkasWitness),
      fs.length = vs.length →
      (∀ fw ∈ fs.zip vs, fw.2.Check source fw.1 guard l u) →
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
          have hw : w.Check source head guard l u := hcheck (head,w) (by simp)
          exact guarded_farkas_sound w source head guard l u hw t hlt htu
            hguard x hx
        · exact ih vs (by simpa using hlen)
            (fun fw hfw => hcheck fw (by simp [hfw])) targetFacet htail
  exact hgo target ws hc.1 hc.2 desired hdesired

/-- A spatial BSP whose leaf implications may use the current angle-guard
sign. Each split is closed on both sides. -/
inductive GuardedSymbolicCoverCertificate where
  | hit (index : ℕ) (witnesses : List GuardedFarkasWitness)
  | split (facet : SymbolicFacet)
      (left right : GuardedSymbolicCoverCertificate)

def GuardedSymbolicCoverCertificate.Check (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (guard : SymbolicQuadratic)
    (l u : ℚ) : GuardedSymbolicCoverCertificate → Prop
  | .hit i ws => i < targets.length ∧
      GuardedPolygonImplicationCheck source (targets.getD i []) ws guard l u
  | .split facet left right =>
      left.Check (facet :: source) targets guard l u ∧
        right.Check (facet.flip :: source) targets guard l u

instance guardedSymbolicCoverCheckDecidable (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (guard : SymbolicQuadratic)
    (l u : ℚ) (c : GuardedSymbolicCoverCertificate) :
    Decidable (c.Check source targets guard l u) := by
  induction c generalizing source with
  | hit i ws =>
      change Decidable (i < targets.length ∧
        GuardedPolygonImplicationCheck source (targets.getD i []) ws guard l u)
      infer_instance
  | split facet left right ihl ihr =>
      letI := ihl (facet :: source)
      letI := ihr (facet.flip :: source)
      change Decidable (left.Check (facet :: source) targets guard l u ∧
        right.Check (facet.flip :: source) targets guard l u)
      infer_instance

theorem guarded_symbolic_cover_sound (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (guard : SymbolicQuadratic)
    (l u : ℚ) (c : GuardedSymbolicCoverCertificate)
    (hc : c.Check source targets guard l u)
    (t : ℝ) (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
    (hguard : 0 ≤ guard.eval t) (x : Point)
    (hx : SymbolicPolygonContains source t x) :
    ∃ target ∈ targets, SymbolicPolygonContains target t x := by
  induction c generalizing source with
  | hit i ws =>
      refine ⟨targets.getD i [], ?_,
        guarded_polygon_implication_sound source (targets.getD i []) ws
          guard l u hc.2 t hlt htu hguard x hx⟩
      rw [List.getD_eq_getElem targets [] hc.1]
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

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.guarded_symbolic_cover_sound
