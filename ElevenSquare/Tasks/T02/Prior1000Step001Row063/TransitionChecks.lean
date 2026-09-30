import ElevenSquare.Tasks.T02.Prior1000Step001Row063.TransitionData
import ElevenSquare.Tasks.T02.RationalChecks

namespace ElevenSquare.Tasks.T02.Prior1000Step001Row063
open ElevenSquare.Pending ElevenSquare.Tasks.T02
noncomputable section
set_option maxRecDepth 100000

theorem transition_self_cuts_checked : ∀ cut ∈ transitionCuts, cut.Check owned6 predecessorRow := by
  rational_decide
theorem transition_domain_implied : BaselinePolygonImplicationCheck (applySelfCuts owned6 predecessorRow transitionCuts).centers inputPolygon domainImplications := by
  rational_decide
theorem transition_input_matches : transition.inputRow predecessorRow = inputRow := rfl
theorem transition_output_matches : transition.outputRows predecessorRow = [retainedRow] := rfl

end
end ElevenSquare.Tasks.T02.Prior1000Step001Row063
