import ElevenSquare.Tasks.T01.Handoff.Groups.G007.MaskBridge

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending ElevenSquare.Pending.CandidateLookup ElevenSquare.Pending.TupleBounds

theorem recorded_case_1540 :
    recordedCaseTuples[1540]! = [0, 1, 4, 5, 6, 7, 10, 11, 12, 13, 14] := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 1540
    (by rw [size_prefix33]; decide)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 1540
    (by rw [size_prefix32]; decide)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 1540
    (by rw [size_prefix31]; decide)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 1540
    (by rw [size_prefix30]; decide)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 1540
    (by rw [size_prefix29]; decide)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 1540
    (by rw [size_prefix28]; decide)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 1540
    (by rw [size_prefix27]; decide)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 1540
    (by rw [size_prefix26]; decide)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 1540
    (by rw [size_prefix25]; decide)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 1540
    (by rw [size_prefix24]; decide)]
  rw [prefix24, lookup_right prefix23 recordedCaseTuplesChunk24 1540
    (by rw [size_prefix23]; decide)
    (by rw [size_prefix23, tuple_block24.1]; decide), size_prefix23]
  rfl

theorem case_mask_1540_of_val (k : Fin 2184)
    (hk : k.val = 1540) : caseMask k = ({0, 1, 4, 5, 6, 7, 10, 11, 12, 13, 14} : Finset (Fin 16)) := by
  have hrow : recordedCaseTuples[k.val]! = [0, 1, 4, 5, 6, 7, 10, 11, 12, 13, 14] := by
    rw [hk]
    exact recorded_case_1540
  calc
    caseMask k = tupleMask [0, 1, 4, 5, 6, 7, 10, 11, 12, 13, 14] :=
      case_mask_of_recorded_case k _ hrow
    _ = _ := by
      simp only [tupleMask, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil]
      rfl

theorem case_mask_1540 :
    caseMask ⟨1540, by decide⟩ = ({0, 1, 4, 5, 6, 7, 10, 11, 12, 13, 14} : Finset (Fin 16)) := by
  exact case_mask_1540_of_val ⟨1540, by decide⟩ rfl

end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.case_mask_1540
