import ElevenSquare.Tasks.T02.RowTransitions
import ElevenSquare.Tasks.T02.StateProgram
import ElevenSquare.Tasks.T02.Exclusion

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- Recorded row updates expose their self-cut/domain conversion obligations;
existing finite ownership and pruning instructions remain reusable. -/
inductive RecordedInstruction where
  | basic (instruction : StateInstruction)
  | rows (owner : Owner) (plan : List (PoseRow × RowTransitionCertificate))

def RecordedInstruction.run (s : PoseState) : RecordedInstruction → PoseState
  | .basic instruction => instruction.run s
  | .rows i plan => replaceRows s i (rowTransitionsOutput plan)

def RecordedInstruction.Check (s : PoseState) : RecordedInstruction → Prop
  | .basic instruction => instruction.Check s
  | .rows i plan => plan.map Prod.fst = s.rows i ∧
      ∀ item ∈ plan, item.2.Check s i item.1

instance recordedInstructionCheckDecidable (s : PoseState) (instruction : RecordedInstruction) :
    Decidable (instruction.Check s) := by
  cases instruction <;> unfold RecordedInstruction.Check <;> infer_instance

theorem recorded_instruction_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (instruction : RecordedInstruction) (hc : instruction.Check s)
    (hs : StateHolds P s) : StateHolds P (instruction.run s) := by
  cases instruction with
  | basic instruction => exact state_instruction_sound P s instruction hc hs
  | rows i plan => exact row_transitions_sound P s i plan hc.1 hc.2 hs

def recordedProgramRun : PoseState → List RecordedInstruction → PoseState
  | s, [] => s
  | s, instruction :: rest => recordedProgramRun (instruction.run s) rest

def RecordedProgramCheck : PoseState → List RecordedInstruction → Prop
  | _, [] => True
  | s, instruction :: rest => instruction.Check s ∧
      RecordedProgramCheck (instruction.run s) rest

instance recordedProgramCheckDecidable (s : PoseState) (program : List RecordedInstruction) :
    Decidable (RecordedProgramCheck s program) := by
  induction program generalizing s with
  | nil => exact inferInstanceAs (Decidable True)
  | cons instruction rest ih =>
    letI := ih (instruction.run s)
    exact inferInstanceAs (Decidable (_ ∧ _))

theorem recorded_program_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (program : List RecordedInstruction) (hc : RecordedProgramCheck s program)
    (hs : StateHolds P s) : StateHolds P (recordedProgramRun s program) := by
  induction program generalizing s with
  | nil => exact hs
  | cons instruction rest ih =>
    exact ih _ hc.2 (recorded_instruction_sound P s instruction hc.1 hs)

theorem checked_recorded_program_refutes {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (program : List RecordedInstruction) (terminal : TerminalCertificate)
    (hp : RecordedProgramCheck s program)
    (ht : terminal.Check (recordedProgramRun s program)) (hs : StateHolds P s) : False :=
  terminal_contradiction P _ (recorded_program_sound P s program hp hs)
    (terminal_certificate_sound _ terminal ht)

def recordedEmptyState : PoseState where
  rows := fun _ => []
  owned := fun _ => []

/-- Adapter to the unchanged public certificate contract. Its empty root is
justified only AFTER the actual initialized, checked program refutes a packing. -/
theorem certificate_from_recorded_program (m : Finset (Fin 16)) (root : PoseState)
    (program : List RecordedInstruction) (terminal : TerminalCertificate)
    (hp : RecordedProgramCheck root program)
    (ht : terminal.Check (recordedProgramRun root program))
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
  exact False.elim (checked_recorded_program_refutes
    (relabelPacking P perm) root program terminal hp ht hs)

end
end ElevenSquare.Tasks.T02
