import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianFiniteCertificate
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicGuardedCover

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A finite median facet with per-site guarded interval signs. The order signs
are paired with the explicit site list, so every site is accounted for. -/
structure GuardedMedianFacetCertificate where
  base : MedianFacetCertificate
  orderSigns : List GuardedSignCertificate

def GuardedMedianFacetCertificate.Check (gc : GuardedMedianFacetCertificate)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half : ℚ) (guard : SymbolicQuadratic) (l u : ℚ) : Prop :=
  let c := gc.base
  0 ≤ half ∧ c.facetIndex < target.length ∧ c.medianSite ∈ sites ∧
  c.sitesList.toFinset = sites ∧
  c.exceptions.card < k ∧
  (c.signU = 1 ∨ c.signU = -1) ∧
  (c.signV = 1 ∨ c.signV = -1) ∧
  let f := target.getD c.facetIndex ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  f.a = c.direction.worldA ∧ f.b = c.direction.worldB ∧
  f.c = c.expectedBound half ∧
  List.Forall₂ (fun p sign => p ∈ c.exceptions ∨
      sign.Check guard
        ((c.direction.projection p).sub
          (c.direction.projection c.medianSite)).quartic l u)
    c.sitesList gc.orderSigns

instance guardedMedianFacetCertificateCheckDecidable
    (gc : GuardedMedianFacetCertificate) (sites : Finset QPoint) (k : ℕ)
    (target : List SymbolicFacet) (half : ℚ)
    (guard : SymbolicQuadratic) (l u : ℚ) :
    Decidable (gc.Check sites k target half guard l u) := by
  unfold GuardedMedianFacetCertificate.Check
  infer_instance

private theorem forall₂_order_choice {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys)
    (x : α) (hx : x ∈ xs) : ∃ y, R x y := by
  induction h with
  | nil => cases hx
  | @cons a b xs ys hab htail ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨b, hab⟩
      · exact ih hx

theorem guarded_median_facet_certificate_sound (gc : GuardedMedianFacetCertificate)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half l u : ℚ) (guard : SymbolicQuadratic)
    (hc : gc.Check sites k target half guard l u)
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (hguard : 0 ≤ guard.eval t) :
    SymbolicMedianFacetWitness sites k q t half
      (gc.base.direction.localNormal q) target := by
  let c := gc.base
  rcases hc with ⟨hhalf, hindex, _, hsites, hcard, hsignU, hsignV,
    hnormA, hnormB, hbound, horders⟩
  let f : SymbolicFacet := target.getD c.facetIndex
    ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  have hmem : f ∈ target := by
    dsimp [f]
    rw [List.getD_eq_getElem target _ hindex]
    exact List.get_mem ..
  have hnormal := c.direction.world_eval q t ha
  have hproj (p : QPoint) :
      (c.direction.projection p).eval t =
        dot (chartNumeratorNormal t (c.direction.localNormal q))
          (realPoint p) := c.direction.projection_eval q p t ha
  have hmedian : MedianLowerBound sites k
      (fun p => dot (chartNumeratorNormal t (c.direction.localNormal q))
        (realPoint p))
      (dot (chartNumeratorNormal t (c.direction.localNormal q))
        (realPoint c.medianSite)) := by
    unfold MedianLowerBound
    have hsubset : sites.filter
        (fun p => dot (chartNumeratorNormal t (c.direction.localNormal q))
            (realPoint p) <
          dot (chartNumeratorNormal t (c.direction.localNormal q))
            (realPoint c.medianSite)) ⊆ c.exceptions := by
      intro p hp
      have hpSite : p ∈ sites := (Finset.mem_filter.mp hp).1
      have hpLt := (Finset.mem_filter.mp hp).2
      have hpList : p ∈ c.sitesList := by
        have : p ∈ c.sitesList.toFinset := by rw [hsites]; exact hpSite
        simpa using this
      obtain ⟨sign, hchoice⟩ := forall₂_order_choice horders p hpList
      rcases hchoice with hexc | hcheck
      · exact hexc
      · have hnonneg := guarded_sign_sound sign guard
          ((c.direction.projection p).sub
            (c.direction.projection c.medianSite)).quartic
          l u hcheck t hlt htu hguard
        rw [symbolic_quadratic_quartic_eval,
          SymbolicQuadratic.sub_eval, hproj p,
          hproj c.medianSite] at hnonneg
        linarith
    exact lt_of_le_of_lt (Finset.card_le_card hsubset) hcard
  refine ⟨f, hmem, 1,
    dot (chartNumeratorNormal t (c.direction.localNormal q))
      (realPoint c.medianSite), by norm_num, ?_, ?_, ?_, hmedian⟩
  · simp only [one_mul]
    rw [hnormA, hnormal]
  · simp only [one_mul]
    rw [hnormB, hnormal]
  · have hu : (c.signU : ℝ) * c.direction.supportU.eval t ≤
        |c.direction.supportU.eval t| := by
      rcases hsignU with hs | hs
      · rw [hs]
        simpa using (le_abs_self (c.direction.supportU.eval t))
      · rw [hs]
        simpa using (neg_le_abs (c.direction.supportU.eval t))
    have hv : (c.signV : ℝ) * c.direction.supportV.eval t ≤
        |c.direction.supportV.eval t| := by
      rcases hsignV with hs | hs
      · rw [hs]
        simpa using (le_abs_self (c.direction.supportV.eval t))
      · rw [hs]
        simpa using (neg_le_abs (c.direction.supportV.eval t))
    have hs := c.direction.support_eval q t ha
    have hfc : f.c.eval t =
        dot (chartNumeratorNormal t (c.direction.localNormal q))
          (realPoint c.medianSite) +
        (half : ℝ) * ((c.signU : ℝ) * c.direction.supportU.eval t +
          (c.signV : ℝ) * c.direction.supportV.eval t) := by
      rw [hbound]
      dsimp [MedianFacetCertificate.expectedBound]
      rw [SymbolicQuadratic.add_eval, SymbolicQuadratic.scale_eval,
        SymbolicQuadratic.add_eval, SymbolicQuadratic.scale_eval,
        SymbolicQuadratic.scale_eval, hproj]
    have hmul := mul_le_mul_of_nonneg_left (add_le_add hu hv)
      (show (0 : ℝ) ≤ half by exact_mod_cast hhalf)
    calc
      f.c.eval t =
          dot (chartNumeratorNormal t (c.direction.localNormal q))
            (realPoint c.medianSite) +
          (half : ℝ) * ((c.signU : ℝ) * c.direction.supportU.eval t +
            (c.signV : ℝ) * c.direction.supportV.eval t) := hfc
      _ ≤ dot (chartNumeratorNormal t (c.direction.localNormal q))
            (realPoint c.medianSite) +
          (half : ℝ) * (|c.direction.supportU.eval t| +
            |c.direction.supportV.eval t|) := by linarith
      _ = 1 * (dot (chartNumeratorNormal t (c.direction.localNormal q))
            (realPoint c.medianSite) + (half : ℝ) * chartDenom t *
              (|(c.direction.localNormal q).1| +
                |(c.direction.localNormal q).2|)) := by rw [hs]; ring

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.guarded_median_facet_certificate_sound
