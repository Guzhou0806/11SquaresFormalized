import ElevenSquare.Tasks.T03.RowsOwnership

namespace ElevenSquare.Pending.T03
noncomputable section

theorem rowsContain_append (left right : List PoseRow) (q : UnitSquare) :
    RowsContain (left++right) q ↔ RowsContain left q ∨ RowsContain right q := by
  constructor
  · rintro ⟨r,hr,hq⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact Or.inl ⟨r,hr,hq⟩
    · exact Or.inr ⟨r,hr,hq⟩
  · rintro (⟨r,hr,hq⟩ | ⟨r,hr,hq⟩)
    · exact ⟨r,List.mem_append_left _ hr,hq⟩
    · exact ⟨r,List.mem_append_right _ hr,hq⟩

theorem rowsContain_cons (row : PoseRow) (rows : List PoseRow) (q : UnitSquare) :
    RowsContain (row::rows) q ↔ row.contains q ∨ RowsContain rows q := by
  constructor
  · rintro ⟨r,hr,hq⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Or.inl hq
    · exact Or.inr ⟨r,hr,hq⟩
  · rintro (hq | ⟨r,hr,hq⟩)
    · exact ⟨row,by simp,hq⟩
    · exact ⟨r,List.mem_cons_of_mem _ hr,hq⟩

/-- A row-local certificate becomes a frozen trace step in its precise owner context. -/
theorem prune_single_row (s : PoseState) (i : Owner) (before after : List PoseRow)
    (old : PoseRow) (newRows : List PoseRow)
    (hrows : s.rows i = before++(old::after)) (hs : RowsOwn s)
    (hback : ∀ q, RowsContain newRows q → old.contains q)
    (hcover : ∀ q, old.contains q →
      (rationalHull (s.owned i) ⊆ {p | OpenSquare q p}) →
      RowsContain newRows q ∨ ∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
        CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q) :
    VerifiedStep s (replaceRows s i (before++(newRows++after))) ∧
    RowsOwn (replaceRows s i (before++(newRows++after))) := by
  have hin (q : UnitSquare) (hq : old.contains q) : RowsContain (s.rows i) q := by
    rw [hrows,rowsContain_append,rowsContain_cons]
    exact Or.inr (Or.inl hq)
  constructor
  · apply VerifiedStep.prunePosewise
    intro q hq
    rw [hrows,rowsContain_append,rowsContain_cons] at hq
    rcases hq with hb | ho | ha
    · exact Or.inl ((rowsContain_append _ _ q).mpr (Or.inl hb))
    · rcases hcover q ho (hs i q (hin q ho)) with hn | hf
      · exact Or.inl ((rowsContain_append _ _ q).mpr
          (Or.inr ((rowsContain_append _ _ q).mpr (Or.inl hn))))
      · exact Or.inr hf
    · exact Or.inl ((rowsContain_append _ _ q).mpr
        (Or.inr ((rowsContain_append _ _ q).mpr (Or.inr ha))))
  · apply rowsOwn_replaceRows s i _ hs
    intro q hq
    rw [rowsContain_append,rowsContain_append] at hq
    rw [hrows,rowsContain_append,rowsContain_cons]
    rcases hq with hb | hn | ha
    · exact Or.inl hb
    · exact Or.inr (Or.inl (hback q hn))
    · exact Or.inr (Or.inr ha)

def intersectCenters (old : PoseRow) (extra : Polygon) : PoseRow :=
  ⟨old.lo,old.hi,extra++old.centers⟩

theorem intersectCenters_contains (old : PoseRow) (extra : Polygon) (q : UnitSquare) :
    (intersectCenters old extra).contains q ↔ old.contains q ∧ q.center ∈ extra.carrier := by
  constructor
  · rintro ⟨hp,ht⟩
    exact ⟨⟨fun l hl => hp l (List.mem_append_right _ hl),ht⟩,
      fun l hl => hp l (List.mem_append_left _ hl)⟩
  · rintro ⟨⟨hp,ht⟩,he⟩
    refine ⟨?_,ht⟩
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact he l hl
    · exact hp l hl

end
end ElevenSquare.Pending.T03
