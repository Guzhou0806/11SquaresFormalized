import ElevenSquare.Tasks.T02.Prior1000Initialization.RootCore
import ElevenSquare.Pending.S06_CandidateMasks

namespace ElevenSquare.Tasks.T02.Prior1000Initialization
open ElevenSquare.Pending ElevenSquare.Tasks.T02
open ElevenSquare.Pending.CandidateLookup ElevenSquare.Pending.TupleBounds
noncomputable section
set_option maxRecDepth 100000

theorem case1000_tuple : recordedCaseTuples[1000]! = [0, 1, 2, 4, 6, 7, 9, 10, 13, 14, 15] := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 1000 (by rw [size_prefix33]; decide)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 1000 (by rw [size_prefix32]; decide)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 1000 (by rw [size_prefix31]; decide)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 1000 (by rw [size_prefix30]; decide)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 1000 (by rw [size_prefix29]; decide)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 1000 (by rw [size_prefix28]; decide)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 1000 (by rw [size_prefix27]; decide)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 1000 (by rw [size_prefix26]; decide)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 1000 (by rw [size_prefix25]; decide)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 1000 (by rw [size_prefix24]; decide)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 1000 (by rw [size_prefix23]; decide)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 1000 (by rw [size_prefix22]; decide)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 1000 (by rw [size_prefix21]; decide)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 1000 (by rw [size_prefix20]; decide)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 1000 (by rw [size_prefix19]; decide)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 1000 (by rw [size_prefix18]; decide)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 1000 (by rw [size_prefix17]; decide)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 1000 (by rw [size_prefix16]; decide)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 1000 (by rw [size_prefix15]; decide)]
  rw [prefix15, lookup_right prefix14 recordedCaseTuplesChunk15 1000
    (by rw [size_prefix14]; decide)
    (by rw [size_prefix14, tuple_block15.1]; decide), size_prefix14]
  rfl

theorem case1000_mask : caseMask 1000 = mask := by
  calc
    caseMask 1000 = candidateTupleMask [0, 1, 2, 4, 6, 7, 9, 10, 13, 14, 15] :=
      caseMask_eq_of_tuple ⟨1000, by decide⟩ _
        (tuple_index_cast recordedCaseTuples 1000 (by decide) _ case1000_tuple)
    _ = mask := by
      simp only [candidateTupleMask, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil]
      rfl

/-- The public numerical case index is tied to the actual literal mask. -/
theorem case1000_initialized (P : Packing 11 coverCap)
    (hc : IsCharted P) (hocc : Occupies P (caseMask 1000)) :
    ∃ perm : Equiv.Perm Owner,
      StateHolds (relabelPacking P perm) archivedRoot :=
  archived_root_initialized P hc (case1000_mask ▸ hocc)

end
end ElevenSquare.Tasks.T02.Prior1000Initialization
