import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicGuardedCover

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A Farkas denominator may vanish at the guard's irrational root. This
certificate permits `denominator = guard * quotient`, with the quotient
strictly positive on the rational interval. It is valid only where the guard
is strictly positive; the opposite branch owns the root itself. -/
structure StrictGuardedFarkasWitness where
  farkas : SymbolicFarkasWitness
  denominatorQuotient : SymbolicQuadratic
  firstSign : GuardedSignCertificate
  secondSign : GuardedSignCertificate
  marginSign : GuardedSignCertificate

def StrictGuardedFarkasWitness.Check (v : StrictGuardedFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet)
    (guard : SymbolicQuadratic) (l u : ℚ) : Prop :=
  let w := v.farkas
  w.first < source.length ∧ w.second < source.length ∧
  let f := source.getD w.first ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  let g := source.getD w.second ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  w.denominator.quartic = guard.mul v.denominatorQuotient ∧
  v.denominatorQuotient.quartic.BernsteinPosCheck l u ∧
  v.firstSign.Check guard w.firstWeight.quartic l u ∧
  v.secondSign.Check guard w.secondWeight.quartic l u ∧
  quarticAdd (w.firstWeight.mul f.a) (w.secondWeight.mul g.a) =
    w.denominator.mul target.a ∧
  quarticAdd (w.firstWeight.mul f.b) (w.secondWeight.mul g.b) =
    w.denominator.mul target.b ∧
  v.marginSign.Check guard (w.margin f g target) l u

instance strictGuardedFarkasCheckDecidable (v : StrictGuardedFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet)
    (guard : SymbolicQuadratic) (l u : ℚ) :
    Decidable (v.Check source target guard l u) := by
  unfold StrictGuardedFarkasWitness.Check
  infer_instance

theorem strict_guarded_farkas_sound (v : StrictGuardedFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet)
    (guard : SymbolicQuadratic) (l u : ℚ)
    (hc : v.Check source target guard l u)
    (t : ℝ) (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
    (hguard : 0 < guard.eval t) (x : Point)
    (hx : SymbolicPolygonContains source t x) : target.contains t x := by
  let w := v.farkas
  let z : SymbolicFacet := ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  let f := source.getD w.first z
  let g := source.getD w.second z
  rcases hc with ⟨hfirst, hsecond, hdenIdentity, hdenQuotient,
    hweight1, hweight2, hnormalA, hnormalB, hmargin⟩
  apply symbolic_farkas_pointwise w source target hfirst hsecond
    hnormalA hnormalB t x hx
  · have hq := quartic_bernstein_pos _ l u hdenQuotient t hlt htu
    have hq' : 0 < v.denominatorQuotient.eval t := by
      simpa only [symbolic_quadratic_quartic_eval] using hq
    have heval : w.denominator.eval t =
        guard.eval t * v.denominatorQuotient.eval t := by
      have he := congrArg (fun q : Quartic => q.eval t) hdenIdentity
      simpa only [symbolic_quadratic_mul_eval,
        symbolic_quadratic_quartic_eval] using he
    rw [heval]
    exact mul_pos hguard hq'
  · have hp := guarded_sign_sound v.firstSign guard w.firstWeight.quartic
      l u hweight1 t hlt htu hguard.le
    simpa only [symbolic_quadratic_quartic_eval] using hp
  · have hp := guarded_sign_sound v.secondSign guard w.secondWeight.quartic
      l u hweight2 t hlt htu hguard.le
    simpa only [symbolic_quadratic_quartic_eval] using hp
  · exact guarded_sign_sound v.marginSign guard (w.margin f g target)
      l u hmargin t hlt htu hguard.le

def StrictGuardedPolygonImplicationCheck (source target : List SymbolicFacet)
    (ws : List StrictGuardedFarkasWitness) (guard : SymbolicQuadratic)
    (l u : ℚ) : Prop :=
  target.length = ws.length ∧
    ∀ fw ∈ target.zip ws, fw.2.Check source fw.1 guard l u

instance strictGuardedPolygonImplicationCheckDecidable
    (source target : List SymbolicFacet) (ws : List StrictGuardedFarkasWitness)
    (guard : SymbolicQuadratic) (l u : ℚ) :
    Decidable (StrictGuardedPolygonImplicationCheck source target ws guard l u) := by
  unfold StrictGuardedPolygonImplicationCheck
  infer_instance

theorem strict_guarded_polygon_implication_sound
    (source target : List SymbolicFacet) (ws : List StrictGuardedFarkasWitness)
    (guard : SymbolicQuadratic) (l u : ℚ)
    (hc : StrictGuardedPolygonImplicationCheck source target ws guard l u)
    (t : ℝ) (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
    (hguard : 0 < guard.eval t) (x : Point)
    (hx : SymbolicPolygonContains source t x) :
    SymbolicPolygonContains target t x := by
  intro desired hdesired
  have hgo : ∀ (fs : List SymbolicFacet) (vs : List StrictGuardedFarkasWitness),
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
          exact strict_guarded_farkas_sound w source head guard l u hw
            t hlt htu hguard x hx
        · exact ih vs (by simpa using hlen)
            (fun fw hfw => hcheck fw (by simp [hfw])) targetFacet htail
  exact hgo target ws hc.1 hc.2 desired hdesired

/-- A spatial BSP for the strict-guard side. Denominators may contain the
guard factor and vanish only on the opposite branch. -/
inductive StrictGuardedSymbolicCoverCertificate where
  | hit (index : ℕ) (witnesses : List StrictGuardedFarkasWitness)
  | split (facet : SymbolicFacet)
      (left right : StrictGuardedSymbolicCoverCertificate)

def StrictGuardedSymbolicCoverCertificate.Check (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (guard : SymbolicQuadratic)
    (l u : ℚ) : StrictGuardedSymbolicCoverCertificate → Prop
  | .hit i ws => i < targets.length ∧
      StrictGuardedPolygonImplicationCheck source (targets.getD i []) ws guard l u
  | .split facet left right =>
      left.Check (facet :: source) targets guard l u ∧
        right.Check (facet.flip :: source) targets guard l u

instance strictGuardedSymbolicCoverCheckDecidable (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (guard : SymbolicQuadratic)
    (l u : ℚ) (c : StrictGuardedSymbolicCoverCertificate) :
    Decidable (c.Check source targets guard l u) := by
  induction c generalizing source with
  | hit i ws =>
      change Decidable (i < targets.length ∧
        StrictGuardedPolygonImplicationCheck source (targets.getD i []) ws guard l u)
      infer_instance
  | split facet left right ihl ihr =>
      letI := ihl (facet :: source)
      letI := ihr (facet.flip :: source)
      change Decidable (left.Check (facet :: source) targets guard l u ∧
        right.Check (facet.flip :: source) targets guard l u)
      infer_instance

theorem strict_guarded_symbolic_cover_sound (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (guard : SymbolicQuadratic)
    (l u : ℚ) (c : StrictGuardedSymbolicCoverCertificate)
    (hc : c.Check source targets guard l u)
    (t : ℝ) (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
    (hguard : 0 < guard.eval t) (x : Point)
    (hx : SymbolicPolygonContains source t x) :
    ∃ target ∈ targets, SymbolicPolygonContains target t x := by
  induction c generalizing source with
  | hit i ws =>
      refine ⟨targets.getD i [], ?_,
        strict_guarded_polygon_implication_sound source (targets.getD i []) ws
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

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.strict_guarded_symbolic_cover_sound
