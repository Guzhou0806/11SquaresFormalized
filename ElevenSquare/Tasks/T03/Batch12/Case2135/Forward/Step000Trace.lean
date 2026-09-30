import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.InitialState
import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step000Rows
import ElevenSquare.Tasks.T03.SemanticCertificate

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step000Trace
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step000Data
noncomputable def state : PoseState := Step000State.state
theorem before_binding : Step000State.refined.rows owner = Step000Rows.certificate.before := by rfl
theorem after_binding : Step000Rows.certificate.after = Step000State.afterRows := by rfl
theorem step_trace : SemanticReplay InitialState.state state := by
  have refineTrace := RefinementRows.trace Step000State.before owner Step000State.entries
    Step000State.partition_checked Step000State.before_binding
  have h := SemanticReplay.forward Step000Rows.certificate Step000State.prior_binding rfl before_binding
  rw [after_binding] at h
  rw [Step000State.state_binding] at h
  exact SemanticReplay.trans (SemanticReplay.verified refineTrace) h
theorem trace : SemanticReplay InitialState.state state :=
  step_trace

end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step000Trace
