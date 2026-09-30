import ElevenSquare.Tasks.T01.Handoff.PlanAPI.Universal

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending

/-- Rational scalar product used to test finite support directions. -/
def rationalDot (normal point : QPoint) : ℚ :=
  normal.1 * point.1 + normal.2 * point.2

/-- A direction exposing two distinct vertices of the difference hull.
    It is enough to test the finite site/core-vertex differences: a linear
    functional has the same maximum on their convex hull as on the list. -/
def ExposedDifferenceFacet (sites core : List QPoint) (normal : QPoint) : Prop :=
  ∃ s₁ ∈ sites, ∃ s₂ ∈ sites, ∃ q₁ ∈ core, ∃ q₂ ∈ core,
    qpointSubtract s₁ q₁ ≠ qpointSubtract s₂ q₂ ∧
    (∀ s ∈ sites, ∀ q ∈ core,
      rationalDot normal (qpointSubtract s q) ≤
        rationalDot normal (qpointSubtract s₁ q₁)) ∧
    rationalDot normal (qpointSubtract s₂ q₂) =
      rationalDot normal (qpointSubtract s₁ q₁)

/-- A support maximizing pair maximizes the site support and minimizes the
    core support separately. -/
theorem difference_support_separates
    (sites core : List QPoint) (normal s₁ q₁ : QPoint)
    (hmax : ∀ s ∈ sites, ∀ q ∈ core,
      rationalDot normal (qpointSubtract s q) ≤
        rationalDot normal (qpointSubtract s₁ q₁))
    (hs₁ : s₁ ∈ sites) (hq₁ : q₁ ∈ core) :
    (∀ s ∈ sites, rationalDot normal s ≤ rationalDot normal s₁) ∧
    (∀ q ∈ core, rationalDot normal q₁ ≤ rationalDot normal q) := by
  constructor
  · intro s hs
    have h := hmax s hs q₁ hq₁
    dsimp [rationalDot, qpointSubtract] at h ⊢
    linarith
  · intro q hq
    have h := hmax s₁ hs₁ q hq
    dsimp [rationalDot, qpointSubtract] at h ⊢
    linarith

/-- Every finite difference-hull facet normal is perpendicular either to a
    pair of distinct sites or to a pair of distinct core vertices. For a
    four-vertex core, using all six pairs avoids any adjacency convention. -/
theorem exposed_difference_facet_normal
    (sites core : List QPoint) (normal : QPoint)
    (h : ExposedDifferenceFacet sites core normal) :
    (∃ s₁ ∈ sites, ∃ s₂ ∈ sites,
      s₁ ≠ s₂ ∧ rationalDot normal (qpointSubtract s₁ s₂) = 0) ∨
    (∃ q₁ ∈ core, ∃ q₂ ∈ core,
      q₁ ≠ q₂ ∧ rationalDot normal (qpointSubtract q₁ q₂) = 0) := by
  obtain ⟨s₁, hs₁, s₂, hs₂, q₁, hq₁, q₂, hq₂, hdistinct, hmax, heq⟩ := h
  obtain ⟨hsite, hcore⟩ :=
    difference_support_separates sites core normal s₁ q₁ hmax hs₁ hq₁
  have hs : rationalDot normal s₁ = rationalDot normal s₂ := by
    have h₁ := hsite s₂ hs₂
    have h₂ := hcore q₂ hq₂
    dsimp [rationalDot] at h₁ h₂
    dsimp [rationalDot, qpointSubtract] at heq ⊢
    linarith
  have hq : rationalDot normal q₁ = rationalDot normal q₂ := by
    have h₁ := hsite s₂ hs₂
    have h₂ := hcore q₂ hq₂
    dsimp [rationalDot] at h₁ h₂
    dsimp [rationalDot, qpointSubtract] at heq ⊢
    linarith
  by_cases hsame : s₁ = s₂
  · right
    refine ⟨q₁, hq₁, q₂, hq₂, ?_, ?_⟩
    · intro hqeq
      apply hdistinct
      simp [hsame, hqeq]
    · dsimp [rationalDot, qpointSubtract] at hq ⊢
      linarith
  · left
    refine ⟨s₁, hs₁, s₂, hs₂, hsame, ?_⟩
    dsimp [rationalDot, qpointSubtract] at hs ⊢
    linarith

end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.exposed_difference_facet_normal
