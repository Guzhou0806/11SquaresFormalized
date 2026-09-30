import ElevenSquare.Tasks.T02.IntegerRowTransitions
import ElevenSquare.Tasks.T02.RecordedProgram

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- An archived row and its explicit integer cover. The predecessor and retained
rows are those of the original transition, not substituted by normalized data. -/
structure IntegerRowRecord where
  predecessor : PoseRow
  transition : RowTransitionCertificate
  cover : IntegerCover.RationalCertificate

def IntegerRowRecord.Check (s : PoseState) (i : Owner) (r : IntegerRowRecord) : Prop :=
  IntegerTransitionCheck s i r.predecessor r.transition r.cover

instance (s : PoseState) (i : Owner) (r : IntegerRowRecord) :
    Decidable (r.Check s i) := by
  unfold IntegerRowRecord.Check
  infer_instance

def integerRowsOutput (rows : List IntegerRowRecord) : List PoseRow :=
  rows.bind (fun r => r.transition.outputRows r.predecessor)

/-- Every predecessor is covered, including closed endpoint ties. The only
geometric information used is the checked state and each record's certificate. -/
theorem integer_rows_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (rows : List IntegerRowRecord)
    (hin : rows.map IntegerRowRecord.predecessor = s.rows i)
    (hc : ∀ r ∈ rows, r.Check s i) (hs : StateHolds P s) :
    StateHolds P (replaceRows s i (integerRowsOutput rows)) := by
  refine ⟨?_, hs.2⟩
  intro j
  by_cases hji : j = i
  · subst j
    obtain ⟨r, hr, hq⟩ := hs.1 i
    rw [← hin] at hr
    obtain ⟨record, hm, rfl⟩ := List.mem_map.mp hr
    obtain ⟨out, hout, hcontains⟩ := integer_row_transition_keeps P s hs i
      record.predecessor record.transition record.cover (hc record hm) hq
    simp only [replaceRows, Function.update_same]
    exact ⟨out, List.mem_bind.mpr ⟨record, hm, hout⟩, hcontains⟩
  · simpa only [replaceRows, Function.update_noteq hji] using hs.1 j

/-- Existing rational/self-cut/ownership instructions and integer row updates
can be composed in one program without changing any shared trace interface. -/
inductive IntegerRecordedInstruction where
  | recorded (instruction : RecordedInstruction)
  | rows (owner : Owner) (records : List IntegerRowRecord)

def IntegerRecordedInstruction.run (s : PoseState) : IntegerRecordedInstruction → PoseState
  | .recorded instruction => instruction.run s
  | .rows i records => replaceRows s i (integerRowsOutput records)

def IntegerRecordedInstruction.Check (s : PoseState) : IntegerRecordedInstruction → Prop
  | .recorded instruction => instruction.Check s
  | .rows i records => records.map IntegerRowRecord.predecessor = s.rows i ∧
      ∀ r ∈ records, r.Check s i

instance (s : PoseState) (instruction : IntegerRecordedInstruction) :
    Decidable (instruction.Check s) := by
  cases instruction <;> unfold IntegerRecordedInstruction.Check <;> infer_instance

theorem integer_recorded_instruction_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (instruction : IntegerRecordedInstruction) (hc : instruction.Check s)
    (hs : StateHolds P s) : StateHolds P (instruction.run s) := by
  cases instruction with
  | recorded instruction => exact recorded_instruction_sound P s instruction hc hs
  | rows i records => exact integer_rows_sound P s i records hc.1 hc.2 hs

def integerRecordedProgramRun : PoseState → List IntegerRecordedInstruction → PoseState
  | s, [] => s
  | s, instruction :: rest => integerRecordedProgramRun (instruction.run s) rest

def IntegerRecordedProgramCheck : PoseState → List IntegerRecordedInstruction → Prop
  | _, [] => True
  | s, instruction :: rest => instruction.Check s ∧
      IntegerRecordedProgramCheck (instruction.run s) rest

instance (s : PoseState) (program : List IntegerRecordedInstruction) :
    Decidable (IntegerRecordedProgramCheck s program) := by
  induction program generalizing s with
  | nil => exact inferInstanceAs (Decidable True)
  | cons instruction rest ih =>
    letI := ih (instruction.run s)
    exact inferInstanceAs (Decidable (_ ∧ _))

theorem integer_recorded_program_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (program : List IntegerRecordedInstruction) (hc : IntegerRecordedProgramCheck s program)
    (hs : StateHolds P s) : StateHolds P (integerRecordedProgramRun s program) := by
  induction program generalizing s with
  | nil => exact hs
  | cons instruction rest ih =>
    exact ih _ hc.2 (integer_recorded_instruction_sound P s instruction hc.1 hs)

theorem integer_recorded_program_run_append (s : PoseState)
    (first second : List IntegerRecordedInstruction) :
    integerRecordedProgramRun s (first ++ second) =
      integerRecordedProgramRun (integerRecordedProgramRun s first) second := by
  induction first generalizing s with
  | nil => rfl
  | cons instruction rest ih => exact ih (instruction.run s)

/-- A suffix is checked at the actual output of its prefix. -/
theorem integer_recorded_program_check_append (s : PoseState)
    (first second : List IntegerRecordedInstruction)
    (hf : IntegerRecordedProgramCheck s first)
    (hs : IntegerRecordedProgramCheck (integerRecordedProgramRun s first) second) :
    IntegerRecordedProgramCheck s (first ++ second) := by
  induction first generalizing s with
  | nil => exact hs
  | cons instruction rest ih => exact ⟨hf.1, ih (instruction.run s) hf.2 hs⟩

theorem checked_integer_recorded_program_refutes {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (program : List IntegerRecordedInstruction)
    (terminal : TerminalCertificate) (hp : IntegerRecordedProgramCheck s program)
    (ht : terminal.Check (integerRecordedProgramRun s program)) (hs : StateHolds P s) :
    False :=
  terminal_contradiction P _ (integer_recorded_program_sound P s program hp hs)
    (terminal_certificate_sound _ terminal ht)

/-- Produce the unchanged public certificate only after a genuinely initialized
checked program refutes every packing for the specified mask. -/
theorem certificate_from_integer_recorded_program (m : Finset (Fin 16))
    (root : PoseState) (program : List IntegerRecordedInstruction)
    (terminal : TerminalCertificate) (hp : IntegerRecordedProgramCheck root program)
    (ht : terminal.Check (integerRecordedProgramRun root program))
    (hroot : ∀ P : Packing 11 coverCap, IsCharted P → Occupies P m →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) root) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P m →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  refine ⟨recordedEmptyState, recordedEmptyState, ?_,
    VerifiedTrace.refl _, Or.inl ⟨0, rfl⟩⟩
  intro P hc ho
  obtain ⟨perm, hs⟩ := hroot P hc ho
  exact False.elim (checked_integer_recorded_program_refutes
    (relabelPacking P perm) root program terminal hp ht hs)

end
end ElevenSquare.Tasks.T02
