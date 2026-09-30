import ElevenSquare.Tasks.T01.Handoff.CaseMaskLookup

namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending

private def tupleMask (row : List ℕ) : Finset (Fin 16) :=
  (row.map (fun j => (⟨j % 16, Nat.mod_lt j (by decide)⟩ : Fin 16))).toFinset

private theorem caseMask_eq_of_tuple (k : Fin 2184) (row : List ℕ)
    (h : recordedCaseTuples[k.val]! = row) : caseMask k = tupleMask row := by
  unfold caseMask tupleMask
  rw [h]

/-- A variable-index form avoids reducing the full source array while a
concrete `Fin` index is elaborated. -/
theorem case_mask_1705_of_val (k : Fin 2184) (hk : k.val = 1705) :
    caseMask k =
      ({0, 2, 3, 4, 5, 7, 8, 9, 10, 13, 15} : Finset (Fin 16)) := by
  have hrow : recordedCaseTuples[k.val]! =
      [0, 2, 3, 4, 5, 7, 8, 9, 10, 13, 15] := by
    rw [hk]
    exact recorded_case_1705
  calc
    caseMask k = tupleMask [0, 2, 3, 4, 5, 7, 8, 9, 10, 13, 15] :=
      caseMask_eq_of_tuple k _ hrow
    _ = _ := by
      simp only [tupleMask, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil]
      rfl

end ElevenSquare.Tasks.T01.Handoff

#print axioms ElevenSquare.Tasks.T01.Handoff.case_mask_1705_of_val
