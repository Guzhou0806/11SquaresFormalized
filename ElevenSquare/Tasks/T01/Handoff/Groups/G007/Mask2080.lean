import ElevenSquare.Tasks.T01.Handoff.Groups.G007.MaskBridge

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending ElevenSquare.Pending.CandidateLookup ElevenSquare.Pending.TupleBounds

theorem recorded_case_2080 :
    recordedCaseTuples[2080]! = [1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14] := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 2080
    (by rw [size_prefix33]; decide)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 2080
    (by rw [size_prefix32]; decide)]
  rw [prefix32, lookup_right prefix31 recordedCaseTuplesChunk32 2080
    (by rw [size_prefix31]; decide)
    (by rw [size_prefix31, tuple_block32.1]; decide), size_prefix31]
  rfl

theorem case_mask_2080_of_val (k : Fin 2184)
    (hk : k.val = 2080) : caseMask k = ({1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14} : Finset (Fin 16)) := by
  have hrow : recordedCaseTuples[k.val]! = [1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14] := by
    rw [hk]
    exact recorded_case_2080
  calc
    caseMask k = tupleMask [1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14] :=
      case_mask_of_recorded_case k _ hrow
    _ = _ := by
      simp only [tupleMask, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil]
      rfl

theorem case_mask_2080 :
    caseMask ⟨2080, by decide⟩ = ({1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14} : Finset (Fin 16)) := by
  exact case_mask_2080_of_val ⟨2080, by decide⟩ rfl

end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.case_mask_2080
