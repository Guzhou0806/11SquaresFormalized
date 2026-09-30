import ElevenSquare.Tasks.T01.Handoff.CaseMaskLookup

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G070
open ElevenSquare.Pending ElevenSquare.Pending.CandidateLookup ElevenSquare.Pending.TupleBounds

def mask : Finset (Fin 16) := {1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 14}
def caseIndex : Fin 2184 := ⟨2127, by decide⟩

theorem recorded_case : recordedCaseTuples[2127]! = [1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 14] := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 2127
    (by rw [size_prefix33]; decide)]
  rw [prefix33, lookup_right prefix32 recordedCaseTuplesChunk33 2127
    (by rw [size_prefix32]; decide)
    (by rw [size_prefix32, tuple_block33.1]; decide), size_prefix32]
  rfl

private def tupleMask (row : List ℕ) : Finset (Fin 16) :=
  (row.map (fun j => (⟨j % 16, Nat.mod_lt j (by decide)⟩ : Fin 16))).toFinset

private theorem caseMask_eq_of_tuple (k : Fin 2184) (row : List ℕ)
    (h : recordedCaseTuples[k.val]! = row) : caseMask k = tupleMask row := by
  unfold caseMask tupleMask
  rw [h]

theorem case_mask_of_val (k : Fin 2184) (hk : k.val = 2127) : caseMask k = mask := by
  have hrow : recordedCaseTuples[k.val]! = [1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 14] := by
    rw [hk]
    exact recorded_case
  calc
    caseMask k = tupleMask [1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 14] := caseMask_eq_of_tuple k _ hrow
    _ = mask := by
      simp only [tupleMask, mask, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil]
      rfl

theorem case_mask : caseMask caseIndex = mask := case_mask_of_val caseIndex rfl

end ElevenSquare.Tasks.T01.Handoff.Groups.G070
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G070.case_mask
