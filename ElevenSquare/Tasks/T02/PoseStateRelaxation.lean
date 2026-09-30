import ElevenSquare.Pending.S05_Trace

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- Only the center region is enlarged; the entire closed angular interval and
all unit-square geometry are unchanged. -/
theorem pose_row_weaken (row : PoseRow) (outer : Polygon)
    (h : row.centers.carrier ⊆ outer.carrier) (q : UnitSquare)
    (hq : row.contains q) : ({row with centers := outer} : PoseRow).contains q :=
  ⟨h hq.1, hq.2⟩

theorem paired_rows_weaken (pairs : List (PoseRow × PoseRow))
    (h : ∀ pair ∈ pairs, ∀ q : UnitSquare, pair.1.contains q → pair.2.contains q)
    (q : UnitSquare) (hq : RowsContain (pairs.map Prod.fst) q) :
    RowsContain (pairs.map Prod.snd) q := by
  obtain ⟨row, hm, hcontains⟩ := hq
  obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hm
  exact ⟨pair.2, List.mem_map.mpr ⟨pair, hp, rfl⟩, h pair hp q hcontains⟩

/-- Ownership remains a separate fact about the actual packing. It is retained,
not re-inferred from an enlarged outer enclosure. -/
theorem state_rows_weaken {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (outer : List PoseRow)
    (h : ∀ q : UnitSquare, RowsContain (s.rows i) q → RowsContain outer q)
    (hs : StateHolds P s) : StateHolds P (replaceRows s i outer) := by
  refine ⟨?_, hs.2⟩
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [replaceRows, Function.update_same] using h (P.squares i) (hs.1 i)
  · simpa only [replaceRows, Function.update_noteq hji] using hs.1 j

end
end ElevenSquare.Tasks.T02
