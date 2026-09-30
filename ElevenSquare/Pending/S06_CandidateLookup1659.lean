import ElevenSquare.Pending.S06_CandidateLookupSupport

namespace ElevenSquare.Pending.CandidateLookup
open TupleBounds

theorem tuple_1659 : recordedCaseTuples[1659]! = [0, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14] := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 1659 (by rw [size_prefix33]; decide)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 1659 (by rw [size_prefix32]; decide)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 1659 (by rw [size_prefix31]; decide)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 1659 (by rw [size_prefix30]; decide)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 1659 (by rw [size_prefix29]; decide)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 1659 (by rw [size_prefix28]; decide)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 1659 (by rw [size_prefix27]; decide)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 1659 (by rw [size_prefix26]; decide)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 1659 (by rw [size_prefix25]; decide)]
  rw [prefix25, lookup_right prefix24 recordedCaseTuplesChunk25 1659
    (by rw [size_prefix24]; decide)
    (by rw [size_prefix24, tuple_block25.1]; decide), size_prefix24]
  rfl

end ElevenSquare.Pending.CandidateLookup
#print axioms ElevenSquare.Pending.CandidateLookup.tuple_1659
