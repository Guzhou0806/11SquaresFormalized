import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianSupportFacet
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianSupportOrder

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

/-- The finite generators of the Minkowski difference of the site and core
    hulls. Duplicate or interior generators are harmless. -/
def pairDifferenceVertices (sites core : List QPoint) : List QPoint :=
  sites.flatMap (fun s => core.map (qpointSubtract s))

/-- A finite, rationally checkable presentation of a difference hull.
    `corners` certifies that the polygon has no points outside the proposed
    vertices. The last two checks identify those vertices with the pairwise
    site/core differences. -/
structure DifferenceHullCertificate (sites core : List QPoint) where
  vertices : List QPoint
  facets : Polygon
  corners : List (ℕ × ℕ)

def DifferenceHullCertificate.Check {sites core : List QPoint}
    (c : DifferenceHullCertificate sites core) : Prop :=
  PolygonCornerCheck c.vertices c.facets c.corners ∧
  (∀ v ∈ c.vertices, v ∈ pairDifferenceVertices sites core) ∧
  (∀ v ∈ pairDifferenceVertices sites core,
    QPointPolygonCheck v c.facets)

instance {sites core : List QPoint} (c : DifferenceHullCertificate sites core) :
    Decidable c.Check := by
  unfold DifferenceHullCertificate.Check
  infer_instance

/-- Every checked presentation is exactly the hull of all pair differences.
    This is the general hull-to-halfplanes bridge used by finite median
    certificates; it does not assume that a generator list is already cyclic
    or free of interior points. -/
theorem DifferenceHullCertificate.check_sound {sites core : List QPoint}
    (c : DifferenceHullCertificate sites core) (hc : c.Check) :
    c.facets.carrier = rationalHull (pairDifferenceVertices sites core) := by
  apply Set.Subset.antisymm
  · intro p hp
    have hvertices : p ∈ rationalHull c.vertices :=
      baseline_polygon_check_sound c.vertices c.facets
        (polygon_corner_check_sound c.vertices c.facets c.corners hc.1) hp
    apply (convexHull_mono (s := {p | ∃ v ∈ c.vertices, p = realPoint v})
      (t := {p | ∃ v ∈ pairDifferenceVertices sites core, p = realPoint v})
      ?_) hvertices
    rintro x ⟨v, hv, rfl⟩
    exact ⟨v, hc.2.1 v hv, rfl⟩
  · exact rationalHull_in_polygon c.facets _ (fun v hv =>
      qpoint_polygon_sound v c.facets (hc.2.2 v hv))

def realRationalDot (normal : QPoint) (point : Point) : ℝ :=
  (normal.1 : ℝ) * point.1 + (normal.2 : ℝ) * point.2

/-- Data needed to turn one finite lower-median bound into the inequality
    associated with a difference-hull facet. The core witness minimizes the
    projection on the finite core vertex list. -/
def MedianFacetBound (sites : Finset QPoint) (k : ℕ) (core : List QPoint)
    (center : Point) (facet : Halfplane) : Prop :=
  ∃ (normal : QPoint) (weight bound : ℚ) (q : QPoint),
    0 ≤ weight ∧
    facet.a = weight * normal.1 ∧
    facet.b = weight * normal.2 ∧
    MedianLowerBound sites k (rationalDot normal) bound ∧
    q ∈ core ∧
    realRationalDot normal center ≤
      (bound : ℝ) - (rationalDot normal q : ℝ)

theorem median_facet_bound_sound
    (sites subset : Finset QPoint) (k : ℕ) (core : List QPoint)
    (center : Point) (facet : Halfplane)
    (hsubset : subset ⊆ sites) (hcard : subset.card = k)
    (hpairs : ∀ v ∈ pairDifferenceVertices subset.toList core,
      QPointPolygonCheck v [facet])
    (hbound : MedianFacetBound sites k core center facet) :
    facet.contains center := by
  obtain ⟨normal, weight, bound, q, hw, ha, hb, hmedian, hq, hcenter⟩ := hbound
  obtain ⟨s, hs, hsb⟩ := median_lower_bound_hits_subset sites subset k
    (rationalDot normal) bound hmedian hsubset hcard
  have hpairmem : qpointSubtract s q ∈ pairDifferenceVertices subset.toList core := by
    apply List.mem_flatMap.mpr
    refine ⟨s, by simpa using hs, ?_⟩
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  have hpair := hpairs _ hpairmem facet (by simp)
  have hr : weight * (rationalDot normal s - rationalDot normal q) ≤ facet.c := by
    dsimp [QPointPolygonCheck, qpointSubtract, rationalDot] at hpair ⊢
    rw [ha, hb] at hpair
    nlinarith [hpair]
  have hqbound : weight * (bound - rationalDot normal q) ≤ facet.c := by
    apply le_trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hsb _) hw)
    exact hr
  have hqreal : (weight : ℝ) * ((bound : ℝ) - (rationalDot normal q : ℝ)) ≤
      (facet.c : ℝ) := by exact_mod_cast hqbound
  have hwreal : (0 : ℝ) ≤ weight := by exact_mod_cast hw
  have hscaled := mul_le_mul_of_nonneg_left hcenter hwreal
  have he : (facet.a : ℝ) * center.1 + (facet.b : ℝ) * center.2 =
      (weight : ℝ) * realRationalDot normal center := by
    rw [ha, hb]
    push_cast
    dsimp [realRationalDot]
    ring
  dsimp [Halfplane.contains]
  rw [he]
  exact hscaled.trans hqreal

/-- Exact finite hull certificates plus median facet bounds place a center
    in the difference hull of every selected `k`-subset. -/
theorem median_difference_hull_membership
    (sites subset : Finset QPoint) (k : ℕ) (core : List QPoint)
    (center : Point) (c : DifferenceHullCertificate subset.toList core)
    (hsubset : subset ⊆ sites) (hcard : subset.card = k)
    (hc : c.Check)
    (hfacets : ∀ facet ∈ c.facets,
      MedianFacetBound sites k core center facet) :
    center ∈ rationalHull (pairDifferenceVertices subset.toList core) := by
  rw [← c.check_sound hc]
  intro facet hf
  exact median_facet_bound_sound sites subset k core center facet hsubset hcard
    (fun v hv f hmem => by
      simp only [List.mem_singleton] at hmem
      subst f
      exact hc.2.2 v hv facet hf)
    (hfacets facet hf)

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.DifferenceHullCertificate.check_sound
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.median_difference_hull_membership
