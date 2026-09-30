import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic

/-! General simplifications of the prior/returned residual certificates.
These theorems do not import any pending packing theorem. -/

namespace ElevenSquare.Pending.T03.Convexification

abbrev Point := ℝ × ℝ

/-- All points belonging to the translated core for every possible center. -/
def commonOffsets (centers core : Set Point) : Set Point :=
  {p | ∀ c ∈ centers, p - c ∈ core}

/-- Enlarging residual localization to its convex hull preserves coverage. -/
theorem convexify_cover {domain forbidden residual : Set Point}
    (h : domain ⊆ forbidden ∪ residual) :
    domain ⊆ forbidden ∪ convexHull ℝ residual := by
  intro p hp
  rcases h hp with hf | hr
  · exact Or.inl hf
  · exact Or.inr (subset_convexHull ℝ residual hr)

/-- Convexifying the possible centers leaves their common translated convex
core exactly unchanged. This is equality, not just a sound weakening. -/
theorem commonOffsets_convexHull (centers core : Set Point)
    (hc : Convex ℝ core) :
    commonOffsets (convexHull ℝ centers) core = commonOffsets centers core := by
  ext p
  constructor
  · intro h c hmem
    exact h c (subset_convexHull ℝ centers hmem)
  · intro h c hmem
    let f : Point →ᵃ[ℝ] Point := AffineMap.const ℝ Point p - AffineMap.id ℝ Point
    have hconv : Convex ℝ {x : Point | p - x ∈ core} := by
      simpa [f] using hc.affine_preimage f
    exact (convexHull_min h hconv) hmem

/-- Every linear lower-bound test on residual centers is equivalent to the
same test on their convex hull. Apply to each core-edge normal. -/
theorem linear_lower_bound_convexHull_iff (centers : Set Point)
    (f : Point → ℝ) (hf : IsLinearMap ℝ f) (b : ℝ) :
    (∀ c ∈ convexHull ℝ centers, b ≤ f c) ↔
      (∀ c ∈ centers, b ≤ f c) := by
  constructor
  · intro h c hc
    exact h c (subset_convexHull ℝ centers hc)
  · intro h c hc
    exact (convexHull_min h (convex_halfspace_ge hf b)) hc

/-- To promote a few chosen points, it suffices to certify those points in
the convex hull of old ownership and a new common core. No complete polygonal
description of that hull is logically required. -/
theorem promote_chosen_points {square old core chosen : Set Point}
    (hs : Convex ℝ square) (hold : old ⊆ square) (hcore : core ⊆ square)
    (hchosen : chosen ⊆ convexHull ℝ (old ∪ core)) :
    convexHull ℝ (old ∪ chosen) ⊆ square := by
  have hunion : old ∪ core ⊆ square := by
    intro p hp
    exact hp.elim (fun h => hold h) (fun h => hcore h)
  have hc : chosen ⊆ square := hchosen.trans (convexHull_min hunion hs)
  apply convexHull_min _ hs
  intro p hp
  exact hp.elim (fun h => hold h) (fun h => hc h)

/-- A two-point witness needs only one scalar weight. It can replace a large
triangulation witness whenever its new endpoint is certified in the core. -/
theorem owned_of_two_points {square : Set Point} (hs : Convex ℝ square)
    {a b : Point} (ha : a ∈ square) (hb : b ∈ square)
    {weight : ℝ} (h0 : 0 ≤ weight) (h1 : weight ≤ 1) :
    (1 - weight) • a + weight • b ∈ square := by
  exact hs ha hb (sub_nonneg.mpr h1) h0 (sub_add_cancel 1 weight)

#print axioms convexify_cover
#print axioms commonOffsets_convexHull
#print axioms linear_lower_bound_convexHull_iff
#print axioms promote_chosen_points
#print axioms owned_of_two_points

end ElevenSquare.Pending.T03.Convexification
