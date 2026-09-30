import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianCanonicalWorld
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianConcreteSupport
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCoverSlab

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

namespace SymbolicQuadratic

def add (p q : SymbolicQuadratic) : SymbolicQuadratic :=
  ⟨p.c0 + q.c0, p.c1 + q.c1, p.c2 + q.c2⟩
def scale (r : ℚ) (p : SymbolicQuadratic) : SymbolicQuadratic :=
  ⟨r * p.c0, r * p.c1, r * p.c2⟩
def sub (p q : SymbolicQuadratic) : SymbolicQuadratic := p.add q.neg

theorem add_eval (p q : SymbolicQuadratic) (t : ℝ) :
    (p.add q).eval t = p.eval t + q.eval t := by
  dsimp [add, eval]
  push_cast
  ring

theorem scale_eval (r : ℚ) (p : SymbolicQuadratic) (t : ℝ) :
    (p.scale r).eval t = r * p.eval t := by
  dsimp [scale, eval]
  push_cast
  ring

theorem sub_eval (p q : SymbolicQuadratic) (t : ℝ) :
    (p.sub q).eval t = p.eval t - q.eval t := by
  rw [sub, add_eval, symbolic_quadratic_neg_eval]
  ring

end SymbolicQuadratic

def chartA : SymbolicQuadratic := ⟨1, 0, -1⟩
def chartB : SymbolicQuadratic := ⟨0, 2, 0⟩
def chartD : SymbolicQuadratic := ⟨1, 0, 1⟩

/-- Four local axes or a signed site-pair perpendicular. -/
inductive MedianDirection where
  | uPos | uNeg | vPos | vNeg
  | pair (a b : QPoint) (negative : Bool)
  deriving DecidableEq

def MedianDirection.localNormal (d : MedianDirection) (q : UnitSquare) : Point :=
  match d with
  | .uPos => (1, 0)
  | .uNeg => (-1, 0)
  | .vPos => (0, 1)
  | .vNeg => (0, -1)
  | .pair a b false => pairPerp q a b
  | .pair a b true => negPoint (pairPerp q a b)

def pairNX (a b : QPoint) : ℚ := b.2 - a.2
def pairNY (a b : QPoint) : ℚ := a.1 - b.1

def MedianDirection.worldA : MedianDirection → SymbolicQuadratic
  | .uPos => chartA
  | .uNeg => chartA.neg
  | .vPos => chartB.neg
  | .vNeg => chartB
  | .pair a b false => SymbolicQuadratic.scaleByChart (pairNX a b)
  | .pair a b true => (SymbolicQuadratic.scaleByChart (pairNX a b)).neg

def MedianDirection.worldB : MedianDirection → SymbolicQuadratic
  | .uPos => chartB
  | .uNeg => chartB.neg
  | .vPos => chartA
  | .vNeg => chartA.neg
  | .pair a b false => SymbolicQuadratic.scaleByChart (pairNY a b)
  | .pair a b true => (SymbolicQuadratic.scaleByChart (pairNY a b)).neg

/-- Cleared numerator of each local component of the normal. -/
def MedianDirection.supportU : MedianDirection → SymbolicQuadratic
  | .uPos | .uNeg | .vPos | .vNeg => chartD
  | .pair a b false => (chartA.scale (pairNX a b)).add (chartB.scale (pairNY a b))
  | .pair a b true => ((chartA.scale (pairNX a b)).add (chartB.scale (pairNY a b))).neg

def MedianDirection.supportV : MedianDirection → SymbolicQuadratic
  | .uPos | .uNeg | .vPos | .vNeg => ⟨0, 0, 0⟩
  | .pair a b false => (chartB.scale (-pairNX a b)).add (chartA.scale (pairNY a b))
  | .pair a b true => ((chartB.scale (-pairNX a b)).add (chartA.scale (pairNY a b))).neg

/-- The two quadratic world-normal coefficients evaluate to the numerator
of the actual local normal. -/
theorem MedianDirection.world_eval (d : MedianDirection) (q : UnitSquare)
    (t : ℝ) (ha : q.axis = chartAxis t) :
    chartNumeratorNormal t (d.localNormal q) =
      (d.worldA.eval t, d.worldB.eval t) := by
  cases d with
  | uPos => apply Prod.ext <;> norm_num [MedianDirection.localNormal, MedianDirection.worldA,
      MedianDirection.worldB, chartNumeratorNormal, chartA, chartB, SymbolicQuadratic.eval] <;> ring
  | uNeg => apply Prod.ext <;> norm_num [MedianDirection.localNormal, MedianDirection.worldA,
      MedianDirection.worldB, chartNumeratorNormal, chartA, chartB,
      SymbolicQuadratic.neg, SymbolicQuadratic.eval] <;> ring
  | vPos => apply Prod.ext <;> norm_num [MedianDirection.localNormal, MedianDirection.worldA,
      MedianDirection.worldB, chartNumeratorNormal, chartA, chartB,
      SymbolicQuadratic.neg, SymbolicQuadratic.eval] <;> ring
  | vNeg => apply Prod.ext <;> norm_num [MedianDirection.localNormal, MedianDirection.worldA,
      MedianDirection.worldB, chartNumeratorNormal, chartA, chartB,
      SymbolicQuadratic.neg, SymbolicQuadratic.eval] <;> ring
  | pair a b negative =>
      cases negative with
      | false =>
          rw [MedianDirection.localNormal, chart_pair_perp_world_normal q t ha a b]
          apply Prod.ext <;> dsimp [MedianDirection.worldA, MedianDirection.worldB,
            pairNX, pairNY] <;> rw [scaled_wall_normal_eval] <;>
            dsimp [chartDenom] <;> push_cast <;> ring
      | true =>
          rw [MedianDirection.localNormal, chart_neg_pair_perp_world_normal q t ha a b]
          apply Prod.ext <;> dsimp [MedianDirection.worldA, MedianDirection.worldB,
            pairNX, pairNY] <;> rw [symbolic_quadratic_neg_eval,
              scaled_wall_normal_eval] <;> dsimp [chartDenom] <;>
            push_cast <;> ring

/-- The two support quadratics clear the denominator of the local L1 norm. -/
theorem MedianDirection.support_eval (d : MedianDirection) (q : UnitSquare)
    (t : ℝ) (ha : q.axis = chartAxis t) :
    |d.supportU.eval t| + |d.supportV.eval t| =
      chartDenom t * (|(d.localNormal q).1| + |(d.localNormal q).2|) := by
  cases d with
  | uPos => simp [MedianDirection.supportU, MedianDirection.supportV,
      MedianDirection.localNormal, chartD, SymbolicQuadratic.eval, chartDenom,
      abs_of_nonneg (show 0 ≤ 1+t^2 by positivity)]
  | uNeg => simp [MedianDirection.supportU, MedianDirection.supportV,
      MedianDirection.localNormal, chartD, SymbolicQuadratic.eval, chartDenom,
      abs_of_nonneg (show 0 ≤ 1+t^2 by positivity)]
  | vPos => simp [MedianDirection.supportU, MedianDirection.supportV,
      MedianDirection.localNormal, chartD, SymbolicQuadratic.eval, chartDenom,
      abs_of_nonneg (show 0 ≤ 1+t^2 by positivity)]
  | vNeg => simp [MedianDirection.supportU, MedianDirection.supportV,
      MedianDirection.localNormal, chartD, SymbolicQuadratic.eval, chartDenom,
      abs_of_nonneg (show 0 ≤ 1+t^2 by positivity)]
  | pair a b negative =>
      cases negative with
      | false =>
          rw [MedianDirection.localNormal,
            chart_pair_perp_local_abs_support q t ha a b]
          dsimp [MedianDirection.supportU, MedianDirection.supportV,
            pairNX, pairNY, chartA, chartB]
          rw [SymbolicQuadratic.add_eval, SymbolicQuadratic.add_eval,
            SymbolicQuadratic.scale_eval, SymbolicQuadratic.scale_eval,
            SymbolicQuadratic.scale_eval, SymbolicQuadratic.scale_eval]
          dsimp [SymbolicQuadratic.eval]
          push_cast
          congr 1 <;> ring

      | true =>
          rw [MedianDirection.localNormal,
            chart_neg_pair_perp_local_abs_support q t ha a b]
          dsimp [MedianDirection.supportU, MedianDirection.supportV,
            pairNX, pairNY, chartA, chartB]
          rw [symbolic_quadratic_neg_eval, symbolic_quadratic_neg_eval,
            abs_neg, abs_neg]
          rw [SymbolicQuadratic.add_eval, SymbolicQuadratic.add_eval,
            SymbolicQuadratic.scale_eval, SymbolicQuadratic.scale_eval,
            SymbolicQuadratic.scale_eval, SymbolicQuadratic.scale_eval]
          dsimp [SymbolicQuadratic.eval]
          push_cast
          congr 1 <;> ring


def MedianDirection.projection (d : MedianDirection) (p : QPoint) :
    SymbolicQuadratic :=
  (d.worldA.scale p.1).add (d.worldB.scale p.2)

theorem MedianDirection.projection_eval (d : MedianDirection) (q : UnitSquare)
    (p : QPoint) (t : ℝ) (ha : q.axis = chartAxis t) :
    (d.projection p).eval t =
      dot (chartNumeratorNormal t (d.localNormal q)) (realPoint p) := by
  rw [MedianDirection.projection, SymbolicQuadratic.add_eval,
    SymbolicQuadratic.scale_eval, SymbolicQuadratic.scale_eval,
    MedianDirection.world_eval d q t ha]
  dsimp [dot, realPoint]
  ring

/-- Finite, exact data for one lower-median support facet. The exception set
may contain fewer than `k` sites; all other sites are certified above the
chosen bound by interval Bernstein checks. Signed support is always at most
the true L1 support, so no sign branch is trusted by the soundness proof. -/
structure MedianFacetCertificate where
  direction : MedianDirection
  facetIndex : ℕ
  medianSite : QPoint
  sitesList : List QPoint
  exceptions : Finset QPoint
  signU : ℚ
  signV : ℚ

def MedianFacetCertificate.expectedBound (c : MedianFacetCertificate)
    (half : ℚ) : SymbolicQuadratic :=
  (c.direction.projection c.medianSite).add
    (((c.direction.supportU.scale c.signU).add
      (c.direction.supportV.scale c.signV)).scale half)

def MedianFacetCertificate.Check (c : MedianFacetCertificate)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half l u : ℚ) : Prop :=
  0 ≤ half ∧ c.facetIndex < target.length ∧ c.medianSite ∈ sites ∧
  c.sitesList.toFinset = sites ∧
  c.exceptions.card < k ∧
  (c.signU = 1 ∨ c.signU = -1) ∧
  (c.signV = 1 ∨ c.signV = -1) ∧
  let f := target.getD c.facetIndex ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  f.a = c.direction.worldA ∧ f.b = c.direction.worldB ∧
  f.c = c.expectedBound half ∧
  c.sitesList.Forall (fun p =>
    p ∈ c.exceptions ∨
      ((c.direction.projection p).sub
        (c.direction.projection c.medianSite)).quartic.BernsteinNonnegCheck l u)

instance medianFacetCertificateCheckDecidable (c : MedianFacetCertificate)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half l u : ℚ) : Decidable (c.Check sites k target half l u) := by
  unfold MedianFacetCertificate.Check
  infer_instance

theorem median_facet_certificate_sound (c : MedianFacetCertificate)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half l u : ℚ) (hc : c.Check sites k target half l u)
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ)) :
    SymbolicMedianFacetWitness sites k q t half
      (c.direction.localNormal q) target := by
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
      have hchoice := (List.forall_iff_forall_mem.mp horders) p hpList
      rcases hchoice with hexc | hcheck
      · exact hexc
      · have hnonneg := quartic_bernstein_nonneg _ l u hcheck t hlt htu
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

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianDirection.world_eval
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianDirection.support_eval
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.median_facet_certificate_sound
