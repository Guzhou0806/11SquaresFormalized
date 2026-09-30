import ElevenSquare.Pending.S06_CandidateLookupSupport

namespace ElevenSquare.Pending.CandidateLookup
open TupleBounds

theorem tuple_1462 : recordedCaseTuples[1462]! = [0, 1, 3, 5, 6, 8, 9, 11, 12, 13, 14] := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 1462 (by rw [size_prefix33]; decide)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 1462 (by rw [size_prefix32]; decide)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 1462 (by rw [size_prefix31]; decide)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 1462 (by rw [size_prefix30]; decide)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 1462 (by rw [size_prefix29]; decide)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 1462 (by rw [size_prefix28]; decide)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 1462 (by rw [size_prefix27]; decide)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 1462 (by rw [size_prefix26]; decide)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 1462 (by rw [size_prefix25]; decide)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 1462 (by rw [size_prefix24]; decide)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 1462 (by rw [size_prefix23]; decide)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 1462 (by rw [size_prefix22]; decide)]
  rw [prefix22, lookup_right prefix21 recordedCaseTuplesChunk22 1462
    (by rw [size_prefix21]; decide)
    (by rw [size_prefix21, tuple_block22.1]; decide), size_prefix21]
  rfl

end ElevenSquare.Pending.CandidateLookup
#print axioms ElevenSquare.Pending.CandidateLookup.tuple_1462
