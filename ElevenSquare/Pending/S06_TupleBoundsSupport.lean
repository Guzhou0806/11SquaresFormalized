import ElevenSquare.Pending.S06_Data
import ElevenSquare.Pending.OrderedData
namespace ElevenSquare.Pending
namespace TupleBounds

def rowsCheck (rows : List (List ℕ)) : Bool :=
  rows.all (fun row => decide (row.length = 11) && row.all (fun j => decide (j < 16)))

theorem rowsCheck_sound (rows : List (List ℕ)) (h : rowsCheck rows = true) :
    ∀ row ∈ rows, row.length = 11 ∧ ∀ j ∈ row, j < 16 := by
  simpa only [rowsCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] using h

def Block (xs : Array (List ℕ)) (n : ℕ) : Prop :=
  xs.size = n ∧ ∀ row ∈ xs.toList, row.length = 11 ∧ ∀ j ∈ row, j < 16

theorem Block.append {xs ys : Array (List ℕ)} {n m : ℕ}
    (hx : Block xs n) (hy : Block ys m) : Block (xs ++ ys) (n + m) := by
  refine ⟨?_, ?_⟩
  · rw [Array.size_append, hx.1, hy.1]
  · intro row hr
    rw [OrderedData.array_toList_append, List.mem_append] at hr
    exact hr.elim (hx.2 row) (hy.2 row)

end TupleBounds
end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.TupleBounds.rowsCheck_sound
#print axioms ElevenSquare.Pending.TupleBounds.Block.append
