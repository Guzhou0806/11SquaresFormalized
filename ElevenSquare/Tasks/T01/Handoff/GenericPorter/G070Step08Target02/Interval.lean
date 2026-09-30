import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02.Cover
import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02.Sound
import ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step04

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression
noncomputable section

theorem owned_matches : Step04.output = owned := by
  norm_num [Step04.output, owned, k0, k1, k2, k3, k4, k5, k6, k7]

/-- Four archived angle bins have one continuum collision certificate against
the already owned hull of physical cell 2. -/
theorem interval_collision (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hl : ((15/32 : ℚ) : ℝ) ≤ t) (hu : t ≤ ((19/32 : ℚ) : ℝ))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell (3 : Fin 16) (normalizeCenter q.center)) :
    ∃ Q : Set Point,
      CoreFits Q q ∧
      q.center ∈ forbiddenCenters (rationalHull Step04.output) Q := by
  rw [owned_matches]
  apply target_sound q t ha hl hu
  apply one_target_cover t hl hu
  exact symbolic_wall_scaled_slab_contains q (3 : Fin 16) t ha hcont hcell

theorem interval_collision_in_state (s : PoseState) (q : UnitSquare) (t : ℝ)
    (howned : s.owned (1 : Owner) = Step04.output)
    (ha : q.axis = chartAxis t)
    (hl : ((15/32 : ℚ) : ℝ) ≤ t) (hu : t ≤ ((19/32 : ℚ) : ℝ))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell (3 : Fin 16) (normalizeCenter q.center)) :
    ∃ Q : Set Point,
      CoreFits Q q ∧
      q.center ∈ forbiddenCenters (rationalHull (s.owned (1 : Owner))) Q := by
  rw [howned]
  exact interval_collision q t ha hl hu hcont hcell

#print axioms interval_collision_in_state

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step08Target02
