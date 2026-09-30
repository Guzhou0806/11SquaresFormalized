import ElevenSquare.Pending.Types
import ElevenSquare.Tasks.T07.CoordinateBridge
import Mathlib.Analysis.Convex.Combination

/-! Pairwise rational vertex differences are sound forbidden-center witnesses.
The certificate field scale is applied only to coordinates, never to physical
unit squares. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
open Pointwise
noncomputable section

def qpointSub (k q : QPoint) : QPoint := (k.1 - q.1, k.2 - q.2)

def pairwiseQDiff (K Q : List QPoint) : List QPoint :=
  (K.product Q).map fun pair => qpointSub pair.1 pair.2

theorem realPoint_qpointSub (k q : QPoint) :
    realPoint (qpointSub k q) = realPoint k - realPoint q := by
  apply Prod.ext <;> simp [qpointSub, realPoint]

/-- Convexifying all exact pairwise vertex differences cannot escape the
Minkowski forbidden-center set formed by the two convex hulls. -/
theorem rationalHull_pairwiseQDiff_subset_forbidden (K Q : List QPoint) :
    rationalHull (pairwiseQDiff K Q) ⊆
      forbiddenCenters (rationalHull K) (rationalHull Q) := by
  let sK : Set Point := {p | ∃ k ∈ K, p = realPoint k}
  let sQ : Set Point := {p | ∃ q ∈ Q, p = realPoint q}
  have hgenerators :
      {p | ∃ v ∈ pairwiseQDiff K Q, p = realPoint v} ⊆ sK - sQ := by
    intro p hp
    rcases hp with ⟨v, hv, rfl⟩
    obtain ⟨⟨k, q⟩, hkq, rfl⟩ := List.mem_map.mp hv
    obtain ⟨hk, hq⟩ := List.mem_product.mp hkq
    rw [realPoint_qpointSub]
    exact ⟨realPoint k, ⟨k, hk, rfl⟩, realPoint q, ⟨q, hq, rfl⟩, rfl⟩
  intro p hp
  have hsub : p ∈ convexHull ℝ (sK - sQ) :=
    convexHull_mono hgenerators hp
  rw [convexHull_sub] at hsub
  rcases hsub with ⟨k, hk, q, hq, hpq⟩
  exact ⟨k, hk, q, hq, hpq.symm⟩

/-- The exact rational certificate scale, kept separate from physical geometry. -/
def fieldScaleRat : ℚ :=
  (191 / 50) / (387708359002281417731 / 100000000000000000000)

theorem fieldScaleRat_cast : (fieldScaleRat : ℝ) = fieldScale := by
  norm_num [fieldScaleRat, fieldScale, coverCap]

def qpointFieldNormalize (p : QPoint) : QPoint :=
  (p.1 / fieldScaleRat, p.2 / fieldScaleRat)

def fieldPhysical (p : Point) : Point :=
  (p.1 / fieldScale, p.2 / fieldScale)

theorem fieldPhysical_toField (p : Point) : fieldPhysical (toField p) = p := by
  apply Prod.ext <;> simp [fieldPhysical, toField, fieldScale_ne_zero]

theorem fieldPhysical_eq_smul (p : Point) :
    fieldPhysical p = (1 / fieldScale) • p := by
  apply Prod.ext <;> simp [fieldPhysical, div_eq_mul_inv, mul_comm]

theorem realPoint_qpointFieldNormalize (p : QPoint) :
    realPoint (qpointFieldNormalize p) = fieldPhysical (realPoint p) := by
  apply Prod.ext <;>
    simp [realPoint, qpointFieldNormalize, fieldPhysical, fieldScaleRat_cast]

/-- Scaling a point in a source rational hull puts it in the hull of the
correspondingly scaled rational vertices. -/
theorem fieldPhysical_rationalHull (vs : List QPoint) (p : Point)
    (hp : p ∈ rationalHull vs) :
    fieldPhysical p ∈ rationalHull (vs.map qpointFieldNormalize) := by
  let G : Set Point := {x | ∃ v ∈ vs, x = realPoint v}
  let G' : Set Point := {x | ∃ v ∈ vs.map qpointFieldNormalize, x = realPoint v}
  have hG : (1 / fieldScale) • G ⊆ G' := by
    intro x hx
    obtain ⟨y, ⟨v, hv, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hx
    refine ⟨qpointFieldNormalize v, List.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [realPoint_qpointFieldNormalize, fieldPhysical_eq_smul]
  have hhull : (1 / fieldScale) • convexHull ℝ G ⊆ convexHull ℝ G' := by
    rw [← convexHull_smul]
    exact convexHull_mono hG
  rw [fieldPhysical_eq_smul]
  exact hhull (Set.smul_mem_smul_set hp)

/-- A field-coordinate pairwise difference is a physical forbidden center
after dividing every source coordinate by the exact certificate scale. -/
theorem fieldPhysical_pairwiseQDiff_forbidden (K Q : List QPoint) (p : Point)
    (hp : p ∈ rationalHull (pairwiseQDiff K Q)) :
    fieldPhysical p ∈ forbiddenCenters
      (rationalHull (K.map qpointFieldNormalize))
      (rationalHull (Q.map qpointFieldNormalize)) := by
  obtain ⟨k, hk, q, hq, hpq⟩ :=
    rationalHull_pairwiseQDiff_subset_forbidden K Q hp
  refine ⟨fieldPhysical k, fieldPhysical_rationalHull K k hk,
    fieldPhysical q, fieldPhysical_rationalHull Q q hq, ?_⟩
  rw [hpq]
  apply Prod.ext <;> dsimp [fieldPhysical] <;> ring

/-- Use this directly after a polygon cover certificate has put `p` inside
the recorded Minkowski polygon and its vertex-difference hull. -/
theorem fieldPolygon_forbidden (K Q : List QPoint) (polygon : Polygon)
    (hpolygon : polygon.carrier ⊆ rationalHull (pairwiseQDiff K Q))
    (p : Point) (hp : p ∈ polygon.carrier) :
    fieldPhysical p ∈ forbiddenCenters
      (rationalHull (K.map qpointFieldNormalize))
      (rationalHull (Q.map qpointFieldNormalize)) :=
  fieldPhysical_pairwiseQDiff_forbidden K Q p (hpolygon hp)

/-- A gift hull may omit redundant pairwise differences; checking membership
of its retained vertices suffices to recover the full difference-hull bound. -/
theorem rationalHull_vertices_subset_pairwiseQDiff
    (K Q vertices : List QPoint)
    (hvertices : ∀ v ∈ vertices, v ∈ pairwiseQDiff K Q) :
    rationalHull vertices ⊆ rationalHull (pairwiseQDiff K Q) := by
  apply convexHull_mono
  rintro p ⟨v, hv, rfl⟩
  exact ⟨v, hvertices v hv, rfl⟩

theorem fieldPolygon_forbidden_of_vertices
    (K Q vertices : List QPoint) (polygon : Polygon)
    (hpolygon : polygon.carrier ⊆ rationalHull vertices)
    (hvertices : ∀ v ∈ vertices, v ∈ pairwiseQDiff K Q)
    (p : Point) (hp : p ∈ polygon.carrier) :
    fieldPhysical p ∈ forbiddenCenters
      (rationalHull (K.map qpointFieldNormalize))
      (rationalHull (Q.map qpointFieldNormalize)) :=
  fieldPolygon_forbidden K Q polygon
    (hpolygon.trans (rationalHull_vertices_subset_pairwiseQDiff K Q vertices hvertices)) p hp

theorem forbiddenCenters_mono {K K' Q Q' : Set Point}
    (hK : K ⊆ K') (hQ : Q ⊆ Q') :
    forbiddenCenters K Q ⊆ forbiddenCenters K' Q' := by
  rintro p ⟨k, hk, q, hq, rfl⟩
  exact ⟨k, hK hk, q, hQ hq, rfl⟩

/-- The form needed by `VerifiedStep.prunePosewise`: a source collision
polygon and pairwise field-vertex differences imply a forbidden *physical*
center, provided the owned and core hulls have been embedded soundly. -/
theorem fieldPolygon_center_forbidden
    (K Q : List QPoint) (polygon : Polygon) (center : Point)
    (owned core : Set Point)
    (hpolygon : polygon.carrier ⊆ rationalHull (pairwiseQDiff K Q))
    (howned : rationalHull (K.map qpointFieldNormalize) ⊆ owned)
    (hcore : rationalHull (Q.map qpointFieldNormalize) ⊆ core)
    (hc : toField center ∈ polygon.carrier) :
    center ∈ forbiddenCenters owned core := by
  have hf := fieldPolygon_forbidden K Q polygon hpolygon
    (toField center) hc
  rw [fieldPhysical_toField] at hf
  exact forbiddenCenters_mono howned hcore hf

end
end ElevenSquare.Tasks.T07
