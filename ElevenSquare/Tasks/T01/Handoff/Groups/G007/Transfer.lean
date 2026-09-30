import ElevenSquare.Tasks.T01.Handoff.Inventory
import ElevenSquare.Combinatorics

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare Pending

/-- The nine occupied cells used by the archived mask-887 certificate. -/
def support : Finset (Fin 16) := {1, 2, 4, 5, 8, 9, 10, 11, 14}

/-- Explicit proposed masks from the exact center-cover source. The statement
    connecting these literals with `caseMask` is a separate outstanding duty. -/
def rosterMasks : List (ℕ × Finset (Fin 16)) := [
  (198, {0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 14}),
  (822, {0, 1, 2, 4, 5, 6, 7, 10, 11, 13, 14}),
  (835, {0, 1, 2, 4, 5, 6, 8, 9, 10, 11, 14}),
  (887, {0, 1, 2, 4, 5, 7, 8, 9, 10, 11, 14}),
  (938, {0, 1, 2, 4, 5, 8, 9, 10, 11, 12, 14}),
  (940, {0, 1, 2, 4, 5, 8, 9, 10, 11, 13, 14}),
  (942, {0, 1, 2, 4, 5, 8, 9, 10, 11, 14, 15}),
  (1217, {0, 1, 3, 4, 5, 6, 7, 10, 11, 13, 14}),
  (1523, {0, 1, 4, 5, 6, 7, 8, 10, 11, 13, 14}),
  (1533, {0, 1, 4, 5, 6, 7, 9, 10, 11, 13, 14}),
  (1540, {0, 1, 4, 5, 6, 7, 10, 11, 12, 13, 14}),
  (2034, {1, 2, 3, 4, 5, 6, 7, 10, 11, 13, 14}),
  (2039, {1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 14}),
  (2060, {1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 14}),
  (2080, {1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14}),
  (2081, {1, 2, 3, 4, 5, 8, 9, 10, 11, 13, 14}),
  (2141, {1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14}),
  (2150, {1, 2, 4, 5, 6, 7, 8, 10, 11, 13, 14}),
  (2153, {1, 2, 4, 5, 6, 7, 9, 10, 11, 13, 14}),
  (2155, {1, 2, 4, 5, 6, 8, 9, 10, 11, 12, 14}),
  (2157, {1, 2, 4, 5, 7, 8, 9, 10, 11, 12, 14})
]

/-- The finite indices coincide with the formalized group roster. -/
theorem roster_indices :
    rosterMasks.map Prod.fst = groupCases (⟨7, by decide⟩ : Group) := by
  decide

/-- A checked finite support/half-turn calculation on the literal masks. -/
theorem literal_support :
    ∀ entry ∈ rosterMasks,
      support ⊆ entry.2 ∨ support ⊆ halfTurnMask entry.2 := by
  decide

end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.literal_support
