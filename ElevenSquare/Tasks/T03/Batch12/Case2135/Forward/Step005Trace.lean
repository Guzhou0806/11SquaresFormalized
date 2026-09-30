import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step004Trace
import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step005Rows
import ElevenSquare.Tasks.T03.SemanticCertificate

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step005Trace
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step005Data
noncomputable def state : PoseState := Step005State.state
theorem before_binding : Step005State.refined.rows owner = Step005Rows.certificate.before := by rfl
theorem after_binding : Step005Rows.certificate.after = Step005State.afterRows := by rfl
theorem step_trace : SemanticReplay Step004Trace.state state := by
  have refineTrace := RefinementRows.trace Step005State.before owner Step005State.entries
    Step005State.partition_checked Step005State.before_binding
  have h := SemanticReplay.forward Step005Rows.certificate Step005State.prior_binding rfl before_binding
  rw [after_binding] at h
  rw [Step005State.state_binding] at h
  exact SemanticReplay.trans (SemanticReplay.verified refineTrace) h
theorem trace : SemanticReplay InitialState.state state :=
  SemanticReplay.trans Step004Trace.trace step_trace

end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step005Trace
