import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCover
import ElevenSquare.Tasks.T01.QuarticScale

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A three-halfplane contradiction. Helly's theorem predicts three as the
largest necessary source subset for an empty planar convex polygon. -/
structure SymbolicEmpty3Witness where
  first : ℕ
  second : ℕ
  third : ℕ
  firstWeight : SymbolicQuadratic
  secondWeight : SymbolicQuadratic
  thirdWeight : SymbolicQuadratic

def SymbolicEmpty3Witness.weightedSum (w : SymbolicEmpty3Witness)
    (a b c : SymbolicQuadratic) : Quartic :=
  quarticAdd (w.firstWeight.mul a)
    (quarticAdd (w.secondWeight.mul b) (w.thirdWeight.mul c))

theorem symbolic_empty3_weighted_sum_eval (w : SymbolicEmpty3Witness)
    (a b c : SymbolicQuadratic) (t : ℝ) :
    (w.weightedSum a b c).eval t =
      w.firstWeight.eval t * a.eval t +
        w.secondWeight.eval t * b.eval t +
        w.thirdWeight.eval t * c.eval t := by
  simp only [SymbolicEmpty3Witness.weightedSum, quartic_add_eval,
    symbolic_quadratic_mul_eval]
  ring

private def zeroSymbolicFacet : SymbolicFacet :=
  ⟨⟨0,0,0⟩, ⟨0,0,0⟩, ⟨0,0,0⟩⟩

def SymbolicEmpty3Witness.Check (w : SymbolicEmpty3Witness)
    (source : List SymbolicFacet) (l u : ℚ) : Prop :=
  w.first < source.length ∧ w.second < source.length ∧
    w.third < source.length ∧
  let f := source.getD w.first zeroSymbolicFacet
  let g := source.getD w.second zeroSymbolicFacet
  let h := source.getD w.third zeroSymbolicFacet
  w.firstWeight.quartic.BernsteinNonnegCheck l u ∧
  w.secondWeight.quartic.BernsteinNonnegCheck l u ∧
  w.thirdWeight.quartic.BernsteinNonnegCheck l u ∧
  w.weightedSum f.a g.a h.a = ⟨0,0,0,0,0⟩ ∧
  w.weightedSum f.b g.b h.b = ⟨0,0,0,0,0⟩ ∧
  ((w.weightedSum f.c g.c h.c).scale (-1)).BernsteinPosCheck l u

instance symbolicEmpty3CheckDecidable (w : SymbolicEmpty3Witness)
    (source : List SymbolicFacet) (l u : ℚ) :
    Decidable (w.Check source l u) := by
  unfold SymbolicEmpty3Witness.Check
  infer_instance

theorem symbolic_empty3_sound (w : SymbolicEmpty3Witness)
    (source : List SymbolicFacet) (l u : ℚ)
    (hc : w.Check source l u) (t : ℝ)
    (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (x : Point) (hx : SymbolicPolygonContains source t x) : False := by
  rcases hc with ⟨hfi, hgi, hhi, hwf, hwg, hwh, hna, hnb, hnegative⟩
  let f := source.getD w.first zeroSymbolicFacet
  let g := source.getD w.second zeroSymbolicFacet
  let h := source.getD w.third zeroSymbolicFacet
  have hf : f.contains t x := hx f (by
    dsimp [f]
    rw [List.getD_eq_get source zeroSymbolicFacet hfi]
    exact List.get_mem ..)
  have hg : g.contains t x := hx g (by
    dsimp [g]
    rw [List.getD_eq_get source zeroSymbolicFacet hgi]
    exact List.get_mem ..)
  have hh : h.contains t x := hx h (by
    dsimp [h]
    rw [List.getD_eq_get source zeroSymbolicFacet hhi]
    exact List.get_mem ..)
  have hfw : 0 ≤ w.firstWeight.eval t := by
    have hp := quartic_bernstein_nonneg _ l u hwf t hlt htu
    simpa only [symbolic_quadratic_quartic_eval] using hp
  have hgw : 0 ≤ w.secondWeight.eval t := by
    have hp := quartic_bernstein_nonneg _ l u hwg t hlt htu
    simpa only [symbolic_quadratic_quartic_eval] using hp
  have hhw : 0 ≤ w.thirdWeight.eval t := by
    have hp := quartic_bernstein_nonneg _ l u hwh t hlt htu
    simpa only [symbolic_quadratic_quartic_eval] using hp
  have ha : w.firstWeight.eval t * f.a.eval t +
      w.secondWeight.eval t * g.a.eval t +
      w.thirdWeight.eval t * h.a.eval t = 0 := by
    have hp := congrArg (fun p : Quartic => p.eval t) hna
    change (w.weightedSum f.a g.a h.a).eval t =
      (⟨0,0,0,0,0⟩ : Quartic).eval t at hp
    rw [symbolic_empty3_weighted_sum_eval] at hp
    simpa [Quartic.eval] using hp
  have hb : w.firstWeight.eval t * f.b.eval t +
      w.secondWeight.eval t * g.b.eval t +
      w.thirdWeight.eval t * h.b.eval t = 0 := by
    have hp := congrArg (fun p : Quartic => p.eval t) hnb
    change (w.weightedSum f.b g.b h.b).eval t =
      (⟨0,0,0,0,0⟩ : Quartic).eval t at hp
    rw [symbolic_empty3_weighted_sum_eval] at hp
    simpa [Quartic.eval] using hp
  have hcneg : w.firstWeight.eval t * f.c.eval t +
      w.secondWeight.eval t * g.c.eval t +
      w.thirdWeight.eval t * h.c.eval t < 0 := by
    have hp := quartic_bernstein_pos _ l u hnegative t hlt htu
    change 0 < ((w.weightedSum f.c g.c h.c).scale (-1)).eval t at hp
    rw [quartic_scale_eval, symbolic_empty3_weighted_sum_eval] at hp
    have hp' : 0 < -(w.firstWeight.eval t * f.c.eval t +
        w.secondWeight.eval t * g.c.eval t +
        w.thirdWeight.eval t * h.c.eval t) := by
      simpa only [Rat.cast_neg, Rat.cast_one, neg_mul, one_mul] using hp
    linarith
  unfold SymbolicFacet.contains at hf hg hh
  have hf' := mul_le_mul_of_nonneg_left hf hfw
  have hg' := mul_le_mul_of_nonneg_left hg hgw
  have hh' := mul_le_mul_of_nonneg_left hh hhw
  have hsum :
      (w.firstWeight.eval t * f.a.eval t +
        w.secondWeight.eval t * g.a.eval t +
        w.thirdWeight.eval t * h.a.eval t) * x.1 +
      (w.firstWeight.eval t * f.b.eval t +
        w.secondWeight.eval t * g.b.eval t +
        w.thirdWeight.eval t * h.b.eval t) * x.2 ≤
      w.firstWeight.eval t * f.c.eval t +
        w.secondWeight.eval t * g.c.eval t +
        w.thirdWeight.eval t * h.c.eval t := by
    calc
      _ = w.firstWeight.eval t *
          (f.a.eval t * x.1 + f.b.eval t * x.2) +
          w.secondWeight.eval t *
          (g.a.eval t * x.1 + g.b.eval t * x.2) +
          w.thirdWeight.eval t *
          (h.a.eval t * x.1 + h.b.eval t * x.2) := by ring
      _ ≤ _ := by exact add_le_add (add_le_add hf' hg') hh'
  rw [ha, hb] at hsum
  nlinarith

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_empty3_sound
