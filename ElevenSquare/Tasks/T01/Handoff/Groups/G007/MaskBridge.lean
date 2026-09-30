import ElevenSquare.Pending.S06_CandidateLookupSupport

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending

def tupleMask (row : List ℕ) : Finset (Fin 16) :=
  (row.map (fun j => (⟨j % 16, Nat.mod_lt j (by decide)⟩ : Fin 16))).toFinset

theorem case_mask_of_recorded_case (k : Fin 2184) (row : List ℕ)
    (h : recordedCaseTuples[k.val]! = row) :
    caseMask k = tupleMask row := by
  unfold caseMask tupleMask
  rw [h]

end ElevenSquare.Tasks.T01.Handoff.Groups.G007
