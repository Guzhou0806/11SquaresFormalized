import ElevenSquare.Tasks.T03.RowRefinement

namespace ElevenSquare.Pending.T03
noncomputable section

def RefinementRows.before (entries : List (IntegerRow × RowRefinement)) : List PoseRow :=
  entries.map (fun e => e.1.row)

def RefinementRows.after (entries : List (IntegerRow × RowRefinement)) : List PoseRow :=
  entries.bind (fun e => (e.2.rows e.1).map IntegerRow.row)

def RefinementRows.check (entries : List (IntegerRow × RowRefinement)) : Bool :=
  entries.all (fun e => e.2.check e.1)

theorem RefinementRows.equiv (entries : List (IntegerRow × RowRefinement))
    (h : RefinementRows.check entries = true) (q : UnitSquare) :
    RowsContain (RefinementRows.before entries) q ↔ RowsContain (RefinementRows.after entries) q := by
  have checked := List.all_eq_true.mp h
  constructor
  · rintro ⟨r,hr,hq⟩
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    obtain ⟨r,hr,hq⟩ := (e.2.equiv e.1 (checked e he) q).mpr hq
    exact ⟨r,List.mem_bind.mpr ⟨e,he,hr⟩,hq⟩
  · rintro ⟨r,hr,hq⟩
    obtain ⟨e,he,hr⟩ := List.mem_bind.mp hr
    exact ⟨e.1.row,List.mem_map.mpr ⟨e,he,rfl⟩,(e.2.equiv e.1 (checked e he) q).mp ⟨r,hr,hq⟩⟩

theorem RefinementRows.trace (s : PoseState) (i : Owner)
    (entries : List (IntegerRow × RowRefinement)) (h : RefinementRows.check entries = true)
    (hb : s.rows i=RefinementRows.before entries) :
    VerifiedTrace s (replaceRows s i (RefinementRows.after entries)) := by
  apply VerifiedTrace.cons (VerifiedStep.outerEquivalent s i (RefinementRows.after entries) ?_)
    (VerifiedTrace.refl _)
  intro q
  rw [hb]
  exact RefinementRows.equiv entries h q

end
end ElevenSquare.Pending.T03
