import ElevenSquare.Tasks.T01.Handoff.Groups.G007.MaskBridge

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending ElevenSquare.Pending.CandidateLookup ElevenSquare.Pending.TupleBounds

theorem recorded_case_835 :
    recordedCaseTuples[835]! = [0, 1, 2, 4, 5, 6, 8, 9, 10, 11, 14] := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 835
    (by rw [size_prefix33]; decide)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 835
    (by rw [size_prefix32]; decide)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 835
    (by rw [size_prefix31]; decide)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 835
    (by rw [size_prefix30]; decide)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 835
    (by rw [size_prefix29]; decide)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 835
    (by rw [size_prefix28]; decide)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 835
    (by rw [size_prefix27]; decide)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 835
    (by rw [size_prefix26]; decide)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 835
    (by rw [size_prefix25]; decide)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 835
    (by rw [size_prefix24]; decide)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 835
    (by rw [size_prefix23]; decide)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 835
    (by rw [size_prefix22]; decide)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 835
    (by rw [size_prefix21]; decide)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 835
    (by rw [size_prefix20]; decide)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 835
    (by rw [size_prefix19]; decide)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 835
    (by rw [size_prefix18]; decide)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 835
    (by rw [size_prefix17]; decide)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 835
    (by rw [size_prefix16]; decide)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 835
    (by rw [size_prefix15]; decide)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 835
    (by rw [size_prefix14]; decide)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 835
    (by rw [size_prefix13]; decide)]
  rw [prefix13, lookup_right prefix12 recordedCaseTuplesChunk13 835
    (by rw [size_prefix12]; decide)
    (by rw [size_prefix12, tuple_block13.1]; decide), size_prefix12]
  rfl

theorem case_mask_835_of_val (k : Fin 2184)
    (hk : k.val = 835) : caseMask k = ({0, 1, 2, 4, 5, 6, 8, 9, 10, 11, 14} : Finset (Fin 16)) := by
  have hrow : recordedCaseTuples[k.val]! = [0, 1, 2, 4, 5, 6, 8, 9, 10, 11, 14] := by
    rw [hk]
    exact recorded_case_835
  calc
    caseMask k = tupleMask [0, 1, 2, 4, 5, 6, 8, 9, 10, 11, 14] :=
      case_mask_of_recorded_case k _ hrow
    _ = _ := by
      simp only [tupleMask, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil]
      rfl

theorem case_mask_835 :
    caseMask ⟨835, by decide⟩ = ({0, 1, 2, 4, 5, 6, 8, 9, 10, 11, 14} : Finset (Fin 16)) := by
  exact case_mask_835_of_val ⟨835, by decide⟩ rfl

end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.case_mask_835
