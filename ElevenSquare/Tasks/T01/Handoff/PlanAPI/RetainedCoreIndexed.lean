import ElevenSquare.Tasks.T01.Handoff.PlanAPI.RetainedCoreFresh

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Promote points after a finite indexed family of retained rows has been
    checked. The row index remains available for its numerical certificate. -/
theorem checked_retained_core_promotion_indexed (s : PoseState) (i : Owner)
    (n : Nat) (row : Fin n → PoseRow) (fresh : List QPoint)
    (coreVertices : Fin n → List QPoint) (corePolygon : Fin n → Polygon)
    (witnesses : Fin n → List RetainedCoreFacetWitness)
    (hrows : s.rows i = (List.finRange n).map row)
    (hcheck : ∀ k : Fin n,
      RetainedCoreFreshCheck (row k) (coreVertices k) (corePolygon k)
        fresh (witnesses k)) :
    VerifiedStep s (replaceHull s i (s.owned i ++ fresh)) := by
  apply VerifiedStep.promoteOwned
  intro q hq hold p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hold (subset_convexHull ℝ _ ⟨p, hp, rfl⟩)
  · obtain ⟨r, hr, hrow⟩ := hq
    rw [hrows] at hr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact retained_core_fresh_sound (row k) (coreVertices k)
      (corePolygon k) fresh (witnesses k) (hcheck k) q hrow p hp

#print axioms checked_retained_core_promotion_indexed

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI
