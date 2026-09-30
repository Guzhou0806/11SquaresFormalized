import ElevenSquare.Pending.S06_CandidateLookupSupport

namespace ElevenSquare.Pending.CandidateLookup
open TupleBounds

theorem tuple_999 : recordedCaseTuples[999]! = [0, 1, 2, 4, 6, 7, 9, 10, 12, 14, 15] := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 999 (by rw [size_prefix33]; decide)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 999 (by rw [size_prefix32]; decide)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 999 (by rw [size_prefix31]; decide)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 999 (by rw [size_prefix30]; decide)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 999 (by rw [size_prefix29]; decide)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 999 (by rw [size_prefix28]; decide)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 999 (by rw [size_prefix27]; decide)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 999 (by rw [size_prefix26]; decide)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 999 (by rw [size_prefix25]; decide)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 999 (by rw [size_prefix24]; decide)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 999 (by rw [size_prefix23]; decide)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 999 (by rw [size_prefix22]; decide)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 999 (by rw [size_prefix21]; decide)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 999 (by rw [size_prefix20]; decide)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 999 (by rw [size_prefix19]; decide)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 999 (by rw [size_prefix18]; decide)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 999 (by rw [size_prefix17]; decide)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 999 (by rw [size_prefix16]; decide)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 999 (by rw [size_prefix15]; decide)]
  rw [prefix15, lookup_right prefix14 recordedCaseTuplesChunk15 999
    (by rw [size_prefix14]; decide)
    (by rw [size_prefix14, tuple_block15.1]; decide), size_prefix14]
  rfl

end ElevenSquare.Pending.CandidateLookup
#print axioms ElevenSquare.Pending.CandidateLookup.tuple_999
