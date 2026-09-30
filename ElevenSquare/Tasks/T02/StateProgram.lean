import ElevenSquare.Tasks.T02.FiniteProgram
import ElevenSquare.Tasks.T02.FiniteSelfCuts

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- Ownership-dependent cuts require their own state-preservation rule. They
are not silently treated as unconditional equivalences of pose-row lists. -/
inductive StateInstruction where
  | trace (instruction : FiniteInstruction)
  | selfCuts (owner : Owner) (plan : List (PoseRow × List SelfHullCut))

def StateInstruction.run (s : PoseState) : StateInstruction → PoseState
  | .trace instr => instr.run s
  | .selfCuts i plan => replaceRows s i (selfCutOutput (s.owned i) plan)

def StateInstruction.Check (s : PoseState) : StateInstruction → Prop
  | .trace instr => instr.Check s
  | .selfCuts i plan => plan.map Prod.fst = s.rows i ∧
      ∀ item ∈ plan, ∀ cut ∈ item.2, cut.Check (s.owned i) item.1

instance stateInstructionCheckDecidable (s : PoseState) (instr : StateInstruction) :
    Decidable (instr.Check s) := by
  cases instr <;> unfold StateInstruction.Check <;> infer_instance

theorem state_instruction_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (instr : StateInstruction) (hc : instr.Check s) (hs : StateHolds P s) :
    StateHolds P (instr.run s) := by
  cases instr with
  | trace instr => exact verified_step_sound P hs (finite_instruction_sound s instr hc)
  | selfCuts i plan => exact self_cut_rows_sound P s i plan hc.1 hc.2 hs

def stateProgramRun : PoseState → List StateInstruction → PoseState
  | s, [] => s
  | s, instr :: rest => stateProgramRun (instr.run s) rest

def StateProgramCheck : PoseState → List StateInstruction → Prop
  | _, [] => True
  | s, instr :: rest => instr.Check s ∧ StateProgramCheck (instr.run s) rest

instance stateProgramCheckDecidable (s : PoseState) (program : List StateInstruction) :
    Decidable (StateProgramCheck s program) := by
  induction program generalizing s with
  | nil => exact inferInstanceAs (Decidable True)
  | cons instr rest ih =>
    letI := ih (instr.run s)
    exact inferInstanceAs (Decidable (_ ∧ _))

theorem state_program_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (program : List StateInstruction) (hc : StateProgramCheck s program)
    (hs : StateHolds P s) : StateHolds P (stateProgramRun s program) := by
  induction program generalizing s with
  | nil => exact hs
  | cons instr rest ih =>
    exact ih _ hc.2 (state_instruction_sound P s instr hc.1 hs)

theorem checked_state_program_refutes {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (program : List StateInstruction) (terminal : TerminalCertificate)
    (hc : StateProgramCheck s program)
    (ht : terminal.Check (stateProgramRun s program)) (hs : StateHolds P s) : False :=
  terminal_contradiction P _ (state_program_sound P s program hc hs)
    (terminal_certificate_sound _ terminal ht)

end
end ElevenSquare.Tasks.T02
