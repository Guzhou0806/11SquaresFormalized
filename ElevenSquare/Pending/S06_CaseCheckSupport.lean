import ElevenSquare.Combinatorics
import ElevenSquare.Pending.S06_Data
import ElevenSquare.Pending.ArrayNodup
namespace ElevenSquare.Pending.CaseChecks
open OrderedData

def rowMask (row : List ℕ) : CellMask :=
  (row.map (fun j => (⟨j % 16, Nat.mod_lt j (by decide)⟩ : Fin 16))).toFinset

def rowKey (row : List ℕ) : ℕ := 65536 - maskWeight (rowMask row)

def rowCheck (row : List ℕ) : Bool :=
  decide ((rowMask row).card = 11 ∧
    maskWeight (halfTurnMask (rowMask row)) ≤ maskWeight (rowMask row))

theorem rowCheck_sound (row : List ℕ) (h : rowCheck row = true) :
    rowMask row ∈ canonicalMasks := by
  exact (mem_canonicalMasks _).mpr (of_decide_eq_true h)

theorem rowsCheck_sound (rows : List (List ℕ)) (h : rows.all rowCheck = true) :
    ∀ row ∈ rows, rowMask row ∈ canonicalMasks := by
  intro row hr
  exact rowCheck_sound row ((List.all_eq_true.mp h) row hr)

end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.rowsCheck_sound
