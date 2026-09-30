import ElevenSquare.Tasks.T01.Field03SymbolicOwnership

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Exact blocker points for this symbolic Field03 regime. -/
def blockerPoints : List QPoint := [((177358160443456420755258087/200000000000000000000000000), (77032697215852719715645569/25000000000000000000000000)), ((124716977/125000000), (720292019/250000000)), ((843756359/1000000000), (726260931/250000000))]

theorem blockerPoints_subset : ∀ p ∈ blockerPoints, p ∈ SharedFieldOwnership.sharedRosterCell12 := by
  intro p hp
  simp only [blockerPoints, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · norm_num [SharedFieldOwnership.sharedRosterCell12]
  · norm_num [SharedFieldOwnership.sharedRosterCell12]
  · norm_num [SharedFieldOwnership.sharedRosterCell12]

theorem blockerPoints_owned (P : Packing 11 coverCap)
    (i j : Owner) (hij : i ≠ j)
    (hother : ClosedCell 12 (normalizeCenter (P.squares j).center))
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (P.squares j).axis = chartAxis t) :
    ∀ p ∈ blockerPoints, ∃ k : Owner, i ≠ k ∧
      OpenSquare (P.squares k) (realPoint p) :=
  field03_cell08_blockers_owned P i j hij hother hchart blockerPoints blockerPoints_subset

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime007.blockerPoints_owned
