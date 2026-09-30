import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step003Trace
import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step004Rows
import ElevenSquare.Tasks.T03.SemanticCertificate

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step004Trace
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step004Data
noncomputable def state : PoseState := Step004State.state
theorem before_binding : Step004State.refined.rows owner = Step004Rows.certificate.before := by rfl
theorem after_binding : Step004Rows.certificate.after = Step004State.afterRows := by rfl
theorem step_trace : SemanticReplay Step003Trace.state state := by
  have refineTrace := RefinementRows.trace Step004State.before owner Step004State.entries
    Step004State.partition_checked Step004State.before_binding
  have h := SemanticReplay.forward Step004Rows.certificate Step004State.prior_binding rfl before_binding
  rw [after_binding] at h
  rw [Step004State.state_binding] at h
  exact SemanticReplay.trans (SemanticReplay.verified refineTrace) h
theorem trace : SemanticReplay InitialState.state state :=
  SemanticReplay.trans Step003Trace.trace step_trace

end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step004Trace
