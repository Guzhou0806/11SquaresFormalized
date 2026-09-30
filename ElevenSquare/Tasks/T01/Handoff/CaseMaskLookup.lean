import ElevenSquare.Pending.S06_CandidateLookupSupport

namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
open ElevenSquare.Pending.CandidateLookup
open ElevenSquare.Pending.TupleBounds

/-- Convert the array's defaulted lookup to its checked lookup once the index
is known to be in range.  This lets case-mask certificates inspect one small
source chunk without reducing the complete 2,184-case array. -/
theorem array_get_bang_eq_getElem {α : Type} [Inhabited α]
    (a : Array α) (i : ℕ) (hi : i < a.size) : a[i]! = a[i]'hi := by
  exact getElem!_pos a i hi

theorem array_get_bang_append_left {α : Type} [Inhabited α]
    (a b : Array α) (i : ℕ) (hi : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  exact lookup_left a b i hi

theorem array_get_bang_append_right {α : Type} [Inhabited α]
    (a b : Array α) (i : ℕ) (hi : a.size ≤ i)
    (hab : i < (a ++ b).size) :
    (a ++ b)[i]! = b[i - a.size]! := by
  have hb : i - a.size < b.size := by
    rw [Array.size_append] at hab
    omega
  exact lookup_right a b i hi hb

/-- The case at index 1705 lies at offset 41 in the 64-row source chunk 26. -/
theorem recorded_case_1705 :
    recordedCaseTuples[1705]! = [0, 2, 3, 4, 5, 7, 8, 9, 10, 13, 15] := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 1705
    (by rw [size_prefix33]; decide)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 1705
    (by rw [size_prefix32]; decide)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 1705
    (by rw [size_prefix31]; decide)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 1705
    (by rw [size_prefix30]; decide)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 1705
    (by rw [size_prefix29]; decide)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 1705
    (by rw [size_prefix28]; decide)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 1705
    (by rw [size_prefix27]; decide)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 1705
    (by rw [size_prefix26]; decide)]
  rw [prefix26, lookup_right prefix25 recordedCaseTuplesChunk26 1705
    (by rw [size_prefix25]; decide)
    (by rw [size_prefix25, tuple_block26.1]; decide), size_prefix25]
  rfl

end ElevenSquare.Tasks.T01.Handoff

#print axioms ElevenSquare.Tasks.T01.Handoff.recorded_case_1705
