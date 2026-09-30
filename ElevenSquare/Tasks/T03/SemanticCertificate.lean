import ElevenSquare.Tasks.T03.ForwardRows

namespace ElevenSquare.Pending.T03
noncomputable section

/-- A semantic replay can discharge the original existential contract once
it has proved that no packing occupies the given cells. The constant empty
state is terminal, and the initialization premise is impossible. This lemma
does not provide the refutation: that remains a separate checked obligation. -/
theorem certificate_of_charted_refutation (m : Finset (Fin 16))
    (h : ∀ P : Packing 11 coverCap, IsCharted P → Occupies P m → False) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P m →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  let s : PoseState := ⟨fun _ => [], fun _ => []⟩
  refine ⟨s,s,?_,VerifiedTrace.refl s,Or.inl ⟨0,rfl⟩⟩
  intro P hchart hocc
  exact False.elim (h P hchart hocc)

/-- Compose sound geometric transitions without the additional row-ownership
invariant required by the restricted public trace constructors. -/
inductive SemanticReplay : PoseState → PoseState → Prop
  | refl (s : PoseState) : SemanticReplay s s
  | row {s : PoseState} {prior : Owner → List QPoint} {rows : Owner → List PoseRow}
      {i : Owner} {chosen : List QPoint} (w : ReplayRows prior rows i chosen)
      (hprior : s.owned=prior) (hrows : s.rows=rows) (hbefore : s.rows i=w.before) :
      SemanticReplay s (replaceHull (replaceRows s i w.after) i chosen)
  | trans {a b c : PoseState} : SemanticReplay a b → SemanticReplay b c → SemanticReplay a c
  | forward {s : PoseState} {prior : Owner → List QPoint} {rows : Owner → List PoseRow}
      {i : Owner} {chosen : List QPoint} (w : ForwardRows prior rows i chosen)
      (hprior : s.owned=prior) (hrows : s.rows=rows) (hbefore : s.rows i=w.before) :
      SemanticReplay s (replaceHull (replaceRows s i w.after) i chosen)
  | verified {a b : PoseState} : VerifiedTrace a b → SemanticReplay a b

theorem SemanticReplay.sound {a b : PoseState} (h : SemanticReplay a b)
    (P : Packing 11 coverCap) (ha : StateHolds P a) : StateHolds P b := by
  induction h with
  | refl => exact ha
  | row w hp hr hb => exact w.sound _ hp hr hb P ha
  | trans hab hbc ihab ihbc => exact ihbc (ihab ha)
  | forward w hp hr hb => exact w.sound _ hp hr hb P ha
  | verified ht => exact verified_trace_sound P ha ht

theorem semantic_replay_certificate (m : Finset (Fin 16)) (a b : PoseState)
    (hi : ∀ P : Packing 11 coverCap, IsCharted P → Occupies P m →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a)
    (ht : SemanticReplay a b) (hb : Terminal b) :
    ∃ s t : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P m →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) s) ∧
      VerifiedTrace s t ∧ Terminal t := by
  apply certificate_of_charted_refutation m
  intro P hchart hocc
  obtain ⟨perm,ha⟩ := hi P hchart hocc
  exact terminal_contradiction (relabelPacking P perm) b (ht.sound _ ha) hb

end
end ElevenSquare.Pending.T03
