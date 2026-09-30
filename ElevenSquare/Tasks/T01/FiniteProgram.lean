import ElevenSquare.Tasks.T01.FinitePruning
import ElevenSquare.Tasks.T01.FiniteOwnership

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

inductive FiniteInstruction where
  | prune (owner : Owner) (plan : List (PoseRow × RowPruningCertificate))
  | ownership (owner : Owner) (certificate : OwnershipCertificate)

def FiniteInstruction.run (s : PoseState) : FiniteInstruction → PoseState
  | .prune i plan => replaceRows s i (pruningOutput plan)
  | .ownership i c => replaceHull s i c.output

def FiniteInstruction.Check (s : PoseState) : FiniteInstruction → Prop
  | .prune i plan => plan.map Prod.fst = s.rows i ∧ ∀ item ∈ plan, item.2.Check s i item.1
  | .ownership i c => c.Check s i

instance (s : PoseState) (instr : FiniteInstruction) : Decidable (instr.Check s) := by
  cases instr <;> unfold FiniteInstruction.Check <;> infer_instance

theorem finite_instruction_sound (s : PoseState) (instr : FiniteInstruction)
    (hc : instr.Check s) : VerifiedStep s (instr.run s) := by
  cases instr with
  | prune i plan => exact checked_pruning_step s i plan hc.1 hc.2
  | ownership i c => exact checked_ownership_step s i c hc

def finiteProgramRun : PoseState → List FiniteInstruction → PoseState
  | s, [] => s
  | s, instr :: rest => finiteProgramRun (instr.run s) rest

def FiniteProgramCheck : PoseState → List FiniteInstruction → Prop
  | _, [] => True
  | s, instr :: rest => instr.Check s ∧ FiniteProgramCheck (instr.run s) rest

instance (s : PoseState) (program : List FiniteInstruction) :
    Decidable (FiniteProgramCheck s program) := by
  induction program generalizing s with
  | nil => exact inferInstanceAs (Decidable True)
  | cons instr rest ih =>
    letI := ih (instr.run s)
    exact inferInstanceAs (Decidable (_ ∧ _))

theorem finite_program_sound (s : PoseState) (program : List FiniteInstruction)
    (hc : FiniteProgramCheck s program) : VerifiedTrace s (finiteProgramRun s program) := by
  induction program generalizing s with
  | nil => exact VerifiedTrace.refl s
  | cons instr rest ih =>
    exact VerifiedTrace.cons (finite_instruction_sound s instr hc.1) (ih _ hc.2)

inductive TerminalCertificate where
  | empty (owner : Owner)
  | collision (left right : Owner) (leftWitness rightWitness : HullWitness)

def TerminalCertificate.Check (s : PoseState) : TerminalCertificate → Prop
  | .empty i => s.rows i = []
  | .collision i j wi wj =>
      i ≠ j ∧ wi.Valid (s.owned i) ∧ wj.Valid (s.owned j) ∧
        wi.eval (s.owned i) = wj.eval (s.owned j)

instance (s : PoseState) (c : TerminalCertificate) : Decidable (c.Check s) := by
  cases c <;> unfold TerminalCertificate.Check <;> infer_instance

theorem terminal_certificate_sound (s : PoseState) (c : TerminalCertificate)
    (hc : c.Check s) : Terminal s := by
  cases c with
  | empty i => exact Or.inl ⟨i, hc⟩
  | collision i j wi wj =>
    refine Or.inr ⟨i, j, hc.1, realPoint (wi.eval (s.owned i)),
      hullWitness_sound _ wi hc.2.1, ?_⟩
    rw [hc.2.2.2]
    exact hullWitness_sound _ wj hc.2.2.1

/-- The replay theorem accepts exact finite checks, with the state after every
instruction computed from its predecessor. Root initialization is a separate duty. -/
theorem checked_program_refutes {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (program : List FiniteInstruction) (terminal : TerminalCertificate)
    (hc : FiniteProgramCheck s program)
    (ht : terminal.Check (finiteProgramRun s program)) : StateHolds P s → False := by
  intro hs
  exact terminal_contradiction P _
    (verified_trace_sound P hs (finite_program_sound s program hc))
    (terminal_certificate_sound _ terminal ht)

end
end ElevenSquare.Tasks.T01
