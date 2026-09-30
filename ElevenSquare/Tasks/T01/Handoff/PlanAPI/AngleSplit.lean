import ElevenSquare.Pending.S05_Trace

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
noncomputable section

/-- Split a pose interval at a rational cut while retaining its exact center
    polygon. Both children include the cut, so no pose is lost there. -/
def splitPoseRow (row : PoseRow) (cut : ℚ) : List PoseRow :=
  [{ lo := row.lo, hi := cut, centers := row.centers },
   { lo := cut, hi := row.hi, centers := row.centers }]

theorem split_pose_row_equiv (row : PoseRow) (cut : ℚ)
    (hlo : row.lo ≤ cut) (hhi : cut ≤ row.hi) (q : UnitSquare) :
    row.contains q ↔ RowsContain (splitPoseRow row cut) q := by
  constructor
  · rintro ⟨hc, t, ht0, ht1, htl, htu, ha⟩
    by_cases htc : t ≤ (cut : ℝ)
    · refine ⟨{ lo := row.lo, hi := cut, centers := row.centers },
        by simp [splitPoseRow], hc, t, ht0, ht1, htl, htc, ha⟩
    · have hct : (cut : ℝ) ≤ t := le_of_lt (lt_of_not_ge htc)
      refine ⟨{ lo := cut, hi := row.hi, centers := row.centers },
        by simp [splitPoseRow], hc, t, ht0, ht1, hct, htu, ha⟩
  · rintro ⟨child, hmem, hc, t, ht0, ht1, htl, htu, ha⟩
    simp only [splitPoseRow, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hleft | hright
    · subst child
      refine ⟨hc, t, ht0, ht1, htl, ?_, ha⟩
      exact htu.trans (by exact_mod_cast hhi)
    · subst child
      refine ⟨hc, t, ht0, ht1, ?_, htu, ha⟩
      have hcut : (row.lo : ℝ) ≤ (cut : ℝ) := by exact_mod_cast hlo
      exact hcut.trans htl

/-- Replace one row in a list with its two closed children. -/
def splitOneRows (before : List PoseRow) (row : PoseRow)
    (after : List PoseRow) (cut : ℚ) : List PoseRow :=
  before ++ splitPoseRow row cut ++ after

theorem split_one_rows_equiv (before after : List PoseRow)
    (row : PoseRow) (cut : ℚ)
    (hlo : row.lo ≤ cut) (hhi : cut ≤ row.hi) (q : UnitSquare) :
    RowsContain (before ++ row :: after) q ↔
      RowsContain (splitOneRows before row after cut) q := by
  constructor
  · rintro ⟨r, hr, hcontains⟩
    simp only [List.mem_append, List.mem_cons] at hr
    rcases hr with hbefore | hr | hafter
    · exact ⟨r, by simp [splitOneRows, hbefore], hcontains⟩
    · subst r
      obtain ⟨child, hchild, hchildcontains⟩ :=
        (split_pose_row_equiv row cut hlo hhi q).mp hcontains
      exact ⟨child, by simp [splitOneRows, hchild], hchildcontains⟩
    · exact ⟨r, by simp [splitOneRows, hafter], hcontains⟩
  · rintro ⟨r, hr, hcontains⟩
    simp only [splitOneRows, List.mem_append] at hr
    rcases hr with (hbefore | hsplit) | hafter
    · exact ⟨r, List.mem_append.mpr (Or.inl hbefore), hcontains⟩
    · have hrow : row.contains q :=
        (split_pose_row_equiv row cut hlo hhi q).mpr
          ⟨r, hsplit, hcontains⟩
      exact ⟨row, List.mem_append.mpr
        (Or.inr (List.mem_cons.mpr (Or.inl rfl))), hrow⟩
    · exact ⟨r, List.mem_append.mpr
        (Or.inr (List.mem_cons.mpr (Or.inr hafter))), hcontains⟩

/-- Splitting an existing state row is an exact outer-cover equivalence, and
    therefore a sound `VerifiedStep` with no packing or container premise. -/
theorem verified_split_one_row (s : PoseState) (i : Owner)
    (before after : List PoseRow) (row : PoseRow) (cut : ℚ)
    (hrows : s.rows i = before ++ row :: after)
    (hlo : row.lo ≤ cut) (hhi : cut ≤ row.hi) :
    VerifiedStep s (replaceRows s i (splitOneRows before row after cut)) := by
  apply VerifiedStep.outerEquivalent
  intro q
  rw [hrows]
  exact split_one_rows_equiv before after row cut hlo hhi q

/-- The indexed version avoids constructing an explicit prefix and suffix for
    a long list of pose bins. -/
theorem verified_split_row_at_index (s : PoseState) (i : Owner)
    (n : ℕ) (hn : n < (s.rows i).length) (cut : ℚ)
    (hlo : (s.rows i)[n].lo ≤ cut)
    (hhi : cut ≤ (s.rows i)[n].hi) :
    VerifiedStep s (replaceRows s i
      (splitOneRows ((s.rows i).take n) (s.rows i)[n]
        ((s.rows i).drop (n + 1)) cut)) := by
  apply verified_split_one_row s i
    ((s.rows i).take n) ((s.rows i).drop (n + 1))
    (s.rows i)[n] cut ?_ hlo hhi
  calc
    s.rows i = (s.rows i).take n ++ (s.rows i).drop n :=
      (List.take_append_drop n (s.rows i)).symm
    _ = (s.rows i).take n ++ (s.rows i)[n] ::
        (s.rows i).drop (n + 1) := by
      rw [← List.cons_getElem_drop_succ (h := hn)]

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.verified_split_one_row
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.verified_split_row_at_index
