import ElevenSquare.Tasks.T02.Prior1000Step000Row037.TransitionData
import ElevenSquare.Tasks.T02.RationalChecks
import ElevenSquare.Tasks.T02.Prior1000Initialization.Cell006.PoseDomains

namespace ElevenSquare.Tasks.T02.Prior1000Step000Row037
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section
set_option maxRecDepth 100000

/-- The predecessor is the actual uncut initial row for seed cell 6, row 37. -/
theorem predecessor_matches_seed :
    predecessorRow = Prior1000Initialization.Cell006.poseCertificate.row 37 := by
  unfold predecessorRow CellRootCertificate.row uniformRow
  congr 1 <;> rational_decide

theorem predecessor_mem_seed_rows :
    predecessorRow ∈ Prior1000Initialization.Cell006.poseCertificate.rows := by
  rw [predecessor_matches_seed]
  exact List.mem_map.mpr ⟨37, by simp, rfl⟩

theorem transition_self_cuts_checked :
    ∀ cut ∈ transitionCuts, cut.Check owned4 predecessorRow := by
  rational_decide

theorem transition_self_cuts_match_archive :
    transitionCuts.map (SelfHullCut.halfplane owned4) = archivedSelfCuts := by
  rational_decide

theorem transition_domain_implied :
    BaselinePolygonImplicationCheck
      (applySelfCuts owned4 predecessorRow transitionCuts).centers
      inputPolygon domainImplications := by
  rational_decide

theorem transition_input_matches : transition.inputRow predecessorRow = inputRow := rfl

theorem transition_output_matches :
    transition.outputRows predecessorRow = [retainedRow] := rfl


end
end ElevenSquare.Tasks.T02.Prior1000Step000Row037
