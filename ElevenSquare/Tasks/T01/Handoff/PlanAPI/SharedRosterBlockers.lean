import ElevenSquare.Tasks.T01.SharedFieldOwnership.Complete
import ElevenSquare.Tasks.T01.Root

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI.SharedRosterBlockers
open ElevenSquare Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A point at a valid gate index is read from the common 188-point roster. -/
def pointsOfRosterIndices (indices : List (Fin 16 × ℕ)) : List QPoint :=
  indices.map (fun item =>
    (SharedFieldOwnership.sharedRoster item.1).getD item.2 (0, 0))

theorem blocker_owned_for_partner (P : Packing 11 coverCap)
    (hc : IsCharted P) (i j : Owner) (hij : i ≠ j)
    (cell : Fin 16)
    (hcell : ClosedCell cell (normalizeCenter (P.squares j).center))
    (p : QPoint) (hp : p ∈ SharedFieldOwnership.sharedRoster cell) :
    ∃ other : Owner, i ≠ other ∧
      OpenSquare (P.squares other) (realPoint p) := by
  exact ⟨j, hij,
    SharedFieldOwnership.shared_roster_full_chart cell (P.squares j)
      hcell (P.contained j) (hc j) p hp⟩

/-- Exact shared gate indices provide blockers owned by distinct squares. -/
theorem roster_index_points_owned (P : Packing 11 coverCap)
    (hc : IsCharted P) (i : Owner)
    (partner : Fin 16 → Owner) (indices : List (Fin 16 × ℕ))
    (hne : ∀ item ∈ indices, i ≠ partner item.1)
    (hcell : ∀ item ∈ indices,
      ClosedCell item.1
        (normalizeCenter (P.squares (partner item.1)).center))
    (hindex : ∀ item ∈ indices,
      item.2 < (SharedFieldOwnership.sharedRoster item.1).length) :
    ∀ p ∈ pointsOfRosterIndices indices,
      ∃ other : Owner, i ≠ other ∧
        OpenSquare (P.squares other) (realPoint p) := by
  intro p hp
  obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hp
  have hpoint :
      (SharedFieldOwnership.sharedRoster item.1).getD item.2 (0, 0) ∈
        SharedFieldOwnership.sharedRoster item.1 := by
    rw [List.getD_eq_getElem _ _ (hindex item hi)]
    exact List.get_mem ..
  exact blocker_owned_for_partner P hc i (partner item.1) (hne item hi)
    item.1 (hcell item hi) _ hpoint

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI.SharedRosterBlockers

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.SharedRosterBlockers.roster_index_points_owned
