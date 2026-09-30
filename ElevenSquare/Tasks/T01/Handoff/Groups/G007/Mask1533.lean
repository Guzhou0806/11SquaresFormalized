import ElevenSquare.Tasks.T01.Handoff.Groups.G007.MaskBridge

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending ElevenSquare.Pending.CandidateLookup ElevenSquare.Pending.TupleBounds

theorem recorded_case_1533 :
    recordedCaseTuples[1533]! = [0, 1, 4, 5, 6, 7, 9, 10, 11, 13, 14] := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 1533
    (by rw [size_prefix33]; decide)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 1533
    (by rw [size_prefix32]; decide)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 1533
    (by rw [size_prefix31]; decide)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 1533
    (by rw [size_prefix30]; decide)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 1533
    (by rw [size_prefix29]; decide)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 1533
    (by rw [size_prefix28]; decide)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 1533
    (by rw [size_prefix27]; decide)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 1533
    (by rw [size_prefix26]; decide)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 1533
    (by rw [size_prefix25]; decide)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 1533
    (by rw [size_prefix24]; decide)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 1533
    (by rw [size_prefix23]; decide)]
  rw [prefix23, lookup_right prefix22 recordedCaseTuplesChunk23 1533
    (by rw [size_prefix22]; decide)
    (by rw [size_prefix22, tuple_block23.1]; decide), size_prefix22]
  rfl

theorem case_mask_1533_of_val (k : Fin 2184)
    (hk : k.val = 1533) : caseMask k = ({0, 1, 4, 5, 6, 7, 9, 10, 11, 13, 14} : Finset (Fin 16)) := by
  have hrow : recordedCaseTuples[k.val]! = [0, 1, 4, 5, 6, 7, 9, 10, 11, 13, 14] := by
    rw [hk]
    exact recorded_case_1533
  calc
    caseMask k = tupleMask [0, 1, 4, 5, 6, 7, 9, 10, 11, 13, 14] :=
      case_mask_of_recorded_case k _ hrow
    _ = _ := by
      simp only [tupleMask, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil]
      rfl

theorem case_mask_1533 :
    caseMask ⟨1533, by decide⟩ = ({0, 1, 4, 5, 6, 7, 9, 10, 11, 13, 14} : Finset (Fin 16)) := by
  exact case_mask_1533_of_val ⟨1533, by decide⟩ rfl

end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.case_mask_1533
