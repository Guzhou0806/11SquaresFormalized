import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell00
import ElevenSquare.Tasks.T01.SharedFieldOwnership.CompleteCell12

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending ElevenSquare.Tasks.T01.SharedFieldOwnership
noncomputable section

/-- Any list of checked cell-0 witnesses blocks another square whose owner is
known to lie in cell 0. The list can change from one angle regime to another. -/
theorem field03_cell04_blockers_owned
    (P : Packing 11 coverCap) (i j : Owner) (hij : i ≠ j)
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (P.squares j).axis = chartAxis t)
    (points : List QPoint)
    (hsubset : ∀ p ∈ points, p ∈ sharedRosterCell00) :
    ∀ p ∈ points, ∃ k : Owner, i ≠ k ∧
      OpenSquare (P.squares k) (realPoint p) := by
  intro p hp
  refine ⟨j, hij, ?_⟩
  exact sharedRosterCell00_owned (P.squares j) hother (P.contained j)
    hchart p (hsubset p hp)

/-- The same ownership transfer for the cell-12 witnesses in cell-8 covers. -/
theorem field03_cell08_blockers_owned
    (P : Packing 11 coverCap) (i j : Owner) (hij : i ≠ j)
    (hother : ClosedCell 12 (normalizeCenter (P.squares j).center))
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (P.squares j).axis = chartAxis t)
    (points : List QPoint)
    (hsubset : ∀ p ∈ points, p ∈ sharedRosterCell12) :
    ∀ p ∈ points, ∃ k : Owner, i ≠ k ∧
      OpenSquare (P.squares k) (realPoint p) := by
  intro p hp
  refine ⟨j, hij, ?_⟩
  exact sharedRosterCell12_owned (P.squares j) hother (P.contained j)
    hchart p (hsubset p hp)

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.field03_cell04_blockers_owned
#print axioms ElevenSquare.Tasks.T01.field03_cell08_blockers_owned
