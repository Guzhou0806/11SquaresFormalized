import ElevenSquare.Tasks.T01.Field03SymbolicOwnership

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Exact blocker points for this symbolic Field03 regime. -/
def blockerPoints : List QPoint := [((498020679/500000000), (997648353/1000000000))]

theorem blockerPoints_subset : ∀ p ∈ blockerPoints, p ∈ SharedFieldOwnership.sharedRosterCell00 := by
  intro p hp
  simp only [blockerPoints, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  · norm_num [SharedFieldOwnership.sharedRosterCell00]

theorem blockerPoints_owned (P : Packing 11 coverCap)
    (i j : Owner) (hij : i ≠ j)
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (P.squares j).axis = chartAxis t) :
    ∀ p ∈ blockerPoints, ∃ k : Owner, i ≠ k ∧
      OpenSquare (P.squares k) (realPoint p) :=
  field03_cell04_blockers_owned P i j hij hother hchart blockerPoints blockerPoints_subset

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012.blockerPoints_owned
