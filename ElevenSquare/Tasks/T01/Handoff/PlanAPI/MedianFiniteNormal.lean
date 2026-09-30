import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianSupportOrder
import ElevenSquare.Pending.S06_BaselinePolyhedral

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

/-- Support inequalities in every real linear direction characterize a finite
    planar hull. This separates the geometric Hahn--Banach step from the
    finite-normal reduction needed for median certificates. -/
theorem finite_hull_of_all_linear_support (vertices : List Point) (center : Point)
    (hsupport : ∀ f : Point →L[ℝ] ℝ,
      ∃ v ∈ vertices, f center ≤ f v) :
    center ∈ convexHull ℝ {v : Point | v ∈ vertices} := by
  have hfinite : ({v : Point | v ∈ vertices} : Set Point).Finite := by
    have heq : {v : Point | v ∈ vertices} =
        (↑vertices.toFinset : Set Point) := by
      ext v
      simp
    rw [heq]
    exact Finset.finite_toSet vertices.toFinset
  have hclosed : IsClosed (convexHull ℝ {v : Point | v ∈ vertices}) :=
    hfinite.isClosed_convexHull ℝ
  have hinside : center ∈ ⋂ f : Point →L[ℝ] ℝ,
      {x | ∃ y ∈ convexHull ℝ {v : Point | v ∈ vertices}, f x ≤ f y} := by
    rw [Set.mem_iInter]
    intro f
    obtain ⟨v, hv, hcv⟩ := hsupport f
    exact ⟨v, subset_convexHull ℝ _ hv, hcv⟩
  rw [iInter_halfSpaces_eq (convex_convexHull ℝ _) hclosed] at hinside
  exact hinside

/-- The same support characterization for rational generators. -/
theorem rational_hull_of_all_linear_support (vertices : List QPoint) (center : Point)
    (hsupport : ∀ f : Point →L[ℝ] ℝ,
      ∃ v ∈ vertices, f center ≤ f (realPoint v)) :
    center ∈ rationalHull vertices := by
  have hinside : center ∈ ⋂ f : Point →L[ℝ] ℝ,
      {x | ∃ y ∈ rationalHull vertices, f x ≤ f y} := by
    rw [Set.mem_iInter]
    intro f
    obtain ⟨v, hv, hcv⟩ := hsupport f
    exact ⟨realPoint v, subset_convexHull ℝ _ ⟨v, hv, rfl⟩, hcv⟩
  change center ∈ ⋂ f : Point →L[ℝ] ℝ,
    {x | ∃ y ∈ convexHull ℝ {p | ∃ v ∈ vertices, p = realPoint v},
      f x ≤ f y} at hinside
  rw [iInter_halfSpaces_eq (convex_convexHull ℝ _)
    (baseline_rationalHull_isClosed vertices)] at hinside
  exact hinside

/-- Every linear functional on the plane is a coordinate dot product. -/
theorem planar_linear_map_eq_dot (f : Point →L[ℝ] ℝ) (p : Point) :
    f p = dot (f (1,0), f (0,1)) p := by
  have hp : p = p.1 • (1,0) + p.2 • (0,1) := by
    ext <;> simp
  rw [hp, map_add, map_smul, map_smul]
  dsimp [dot]
  ring

/-- Dot-product support inequalities imply membership in a finite planar
    convex hull. The normal may be any real vector. -/
theorem finite_hull_of_all_dot_support (vertices : List Point) (center : Point)
    (hsupport : ∀ normal : Point,
      ∃ v ∈ vertices, dot normal center ≤ dot normal v) :
    center ∈ convexHull ℝ {v : Point | v ∈ vertices} := by
  apply finite_hull_of_all_linear_support vertices center
  intro f
  obtain ⟨v, hv, hcv⟩ := hsupport (f (1,0), f (0,1))
  refine ⟨v, hv, ?_⟩
  rw [planar_linear_map_eq_dot f center, planar_linear_map_eq_dot f v]
  exact hcv

theorem rational_hull_of_all_dot_support (vertices : List QPoint) (center : Point)
    (hsupport : ∀ normal : Point,
      ∃ v ∈ vertices, dot normal center ≤ dot normal (realPoint v)) :
    center ∈ rationalHull vertices := by
  apply rational_hull_of_all_linear_support vertices center
  intro f
  obtain ⟨v, hv, hcv⟩ := hsupport (f (1,0), f (0,1))
  refine ⟨v, hv, ?_⟩
  rw [planar_linear_map_eq_dot f center, planar_linear_map_eq_dot f (realPoint v)]
  exact hcv

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.finite_hull_of_all_linear_support
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.rational_hull_of_all_linear_support
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.finite_hull_of_all_dot_support
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.rational_hull_of_all_dot_support
