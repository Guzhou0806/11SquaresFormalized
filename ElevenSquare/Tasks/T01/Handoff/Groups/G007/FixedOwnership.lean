import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate.OwnedRosterProof

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedOwnership
open ElevenSquare Pending ElevenSquare.Tasks.T01.Handoff.Groups.G007.Candidate
noncomputable section

/-- A blocker selected from the checked G007 roster belongs to the square
assigned to its physical cell throughout the full angle chart. -/
theorem blocker_owned_for_partner (P : Packing 11 coverCap)
    (hc : IsCharted P) (i j : Owner) (hij : i ≠ j)
    (cell : Fin 16)
    (hcell : ClosedCell cell (normalizeCenter (P.squares j).center))
    (p : QPoint) (hp : p ∈ ownedRoster cell) :
    ∃ other : Owner, i ≠ other ∧ OpenSquare (P.squares other) (realPoint p) := by
  exact ⟨j, hij, owned_roster_full_chart cell (P.squares j) hcell
    (P.contained j) (hc j) p hp⟩

/-- The geometric blocker list is obtained from exact roster indices. -/
def pointsOfRosterIndices (indices : List (Fin 16 × ℕ)) : List QPoint :=
  indices.map (fun item => (ownedRoster item.1).getD item.2 (0, 0))

theorem roster_index_points_owned (P : Packing 11 coverCap)
    (hc : IsCharted P) (i : Owner)
    (partner : Fin 16 → Owner) (indices : List (Fin 16 × ℕ))
    (hne : ∀ item ∈ indices, i ≠ partner item.1)
    (hcell : ∀ item ∈ indices,
      ClosedCell item.1 (normalizeCenter (P.squares (partner item.1)).center))
    (hindex : ∀ item ∈ indices, item.2 < (ownedRoster item.1).length) :
    ∀ p ∈ pointsOfRosterIndices indices,
      ∃ other : Owner, i ≠ other ∧ OpenSquare (P.squares other) (realPoint p) := by
  intro p hp
  obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hp
  have hpoint : (ownedRoster item.1).getD item.2 (0, 0) ∈ ownedRoster item.1 := by
    rw [List.getD_eq_getElem _ _ (hindex item hi)]
    exact List.get_mem ..
  exact blocker_owned_for_partner P hc i (partner item.1) (hne item hi)
    item.1 (hcell item hi) _ hpoint

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedOwnership

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedOwnership.roster_index_points_owned
