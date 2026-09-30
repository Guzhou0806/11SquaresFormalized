import ElevenSquare.Tasks.T03.Promotion

namespace ElevenSquare.Pending.T03
noncomputable section

/-- This stronger invariant is proved from refined initial rows; it is not an
extra hypothesis inserted into any frozen trace constructor. -/
def RowsOwn (s : PoseState) : Prop :=
  ∀ i q, RowsContain (s.rows i) q → rationalHull (s.owned i) ⊆ {p | OpenSquare q p}

theorem rowsOwn_replaceRows (s : PoseState) (i : Owner) (rs : List PoseRow)
    (hs : RowsOwn s) (hback : ∀ q, RowsContain rs q → RowsContain (s.rows i) q) :
    RowsOwn (replaceRows s i rs) := by
  intro j q hq
  by_cases hji : j = i
  · subst j
    have hr : RowsContain rs q := by simpa [replaceRows] using hq
    exact hs i q (hback q hr)
  · have hr : RowsContain (s.rows j) q := by
      simpa [replaceRows,Function.update_noteq hji] using hq
    exact hs j q hr

theorem rowsOwn_replaceHull (s : PoseState) (i : Owner) (vs : List QPoint)
    (hs : RowsOwn s)
    (hv : ∀ q, RowsContain (s.rows i) q → ∀ v ∈ vs, OpenSquare q (realPoint v)) :
    RowsOwn (replaceHull s i vs) := by
  intro j q hq
  by_cases hji : j = i
  · subst j
    simpa [replaceHull] using hull_owned_of_vertices q vs (hv q hq)
  · simpa [replaceHull,Function.update_noteq hji] using hs j q hq

theorem promote_preserving_rowsOwn (s : PoseState) (i : Owner) (vs : List QPoint)
    (hs : RowsOwn s)
    (hv : ∀ q, RowsContain (s.rows i) q →
      rationalHull (s.owned i) ⊆ {p | OpenSquare q p} →
      ∀ v ∈ vs, OpenSquare q (realPoint v)) :
    VerifiedStep s (replaceHull s i vs) ∧ RowsOwn (replaceHull s i vs) := by
  have hv' := fun q hq => hv q hq (hs i q hq)
  exact ⟨VerifiedStep.promote s i vs hv',rowsOwn_replaceHull s i vs hs hv'⟩

def addCenterPlane (r : PoseRow) (l : Halfplane) : PoseRow :=
  ⟨r.lo,r.hi,l::r.centers⟩

theorem addCenterPlane_contains (r : PoseRow) (l : Halfplane) (q : UnitSquare) :
    (addCenterPlane r l).contains q ↔ r.contains q ∧ l.contains q.center := by
  constructor
  · rintro ⟨hc,ht⟩
    refine ⟨⟨?_,ht⟩,hc l (by simp [addCenterPlane])⟩
    intro k hk
    exact hc k (List.mem_cons_of_mem l hk)
  · rintro ⟨⟨hc,ht⟩,hl⟩
    refine ⟨?_,ht⟩
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hl
    · exact hc k hk

theorem addCenterPlane_rows (rows : List PoseRow) (l : Halfplane) (q : UnitSquare) :
    RowsContain (rows.map (fun r => addCenterPlane r l)) q ↔
      RowsContain rows q ∧ l.contains q.center := by
  constructor
  · rintro ⟨r,hr,hq⟩
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hr
    obtain ⟨hq,hl⟩ := (addCenterPlane_contains old l q).mp hq
    exact ⟨⟨old,hold,hq⟩,hl⟩
  · rintro ⟨⟨r,hr,hq⟩,hl⟩
    exact ⟨addCenterPlane r l,List.mem_map.mpr ⟨r,hr,rfl⟩,
      (addCenterPlane_contains r l q).mpr ⟨hq,hl⟩⟩

theorem center_cut_step (s : PoseState) (i : Owner) (l : Halfplane)
    (hs : RowsOwn s)
    (hl : ∀ q, RowsContain (s.rows i) q →
      rationalHull (s.owned i) ⊆ {p | OpenSquare q p} → l.contains q.center) :
    VerifiedStep s (replaceRows s i ((s.rows i).map (fun r => addCenterPlane r l))) ∧
    RowsOwn (replaceRows s i ((s.rows i).map (fun r => addCenterPlane r l))) := by
  have heq : ∀ q, RowsContain (s.rows i) q ↔
      RowsContain ((s.rows i).map (fun r => addCenterPlane r l)) q := by
    intro q
    rw [addCenterPlane_rows]
    exact ⟨fun hq => ⟨hq,hl q hq (hs i q hq)⟩,fun hq => hq.1⟩
  exact ⟨VerifiedStep.outerEquivalent s i _ heq,
    rowsOwn_replaceRows s i _ hs (fun q hq => (heq q).mpr hq)⟩

end
end ElevenSquare.Pending.T03
