import ElevenSquare.Tasks.T01.Handoff.Groups.G007.MaskBridge

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending ElevenSquare.Pending.CandidateLookup ElevenSquare.Pending.TupleBounds

theorem recorded_case_2141 :
    recordedCaseTuples[2141]! = [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14] := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 2141
    (by rw [size_prefix33]; decide)]
  rw [prefix33, lookup_right prefix32 recordedCaseTuplesChunk33 2141
    (by rw [size_prefix32]; decide)
    (by rw [size_prefix32, tuple_block33.1]; decide), size_prefix32]
  rfl

theorem case_mask_2141_of_val (k : Fin 2184)
    (hk : k.val = 2141) : caseMask k = ({1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14} : Finset (Fin 16)) := by
  have hrow : recordedCaseTuples[k.val]! = [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14] := by
    rw [hk]
    exact recorded_case_2141
  calc
    caseMask k = tupleMask [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14] :=
      case_mask_of_recorded_case k _ hrow
    _ = _ := by
      simp only [tupleMask, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil]
      rfl

theorem case_mask_2141 :
    caseMask ⟨2141, by decide⟩ = ({1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14} : Finset (Fin 16)) := by
  exact case_mask_2141_of_val ⟨2141, by decide⟩ rfl

end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.case_mask_2141
