import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step002Trace
import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step003Rows
import ElevenSquare.Tasks.T03.SemanticCertificate

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Trace
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step003Data
noncomputable def state : PoseState := Step003State.state
theorem before_binding : Step003State.refined.rows owner = Step003Rows.certificate.before := by rfl
theorem after_binding : Step003Rows.certificate.after = Step003State.afterRows := by rfl
theorem step_trace : SemanticReplay Step002Trace.state state := by
  have refineTrace := RefinementRows.trace Step003State.before owner Step003State.entries
    Step003State.partition_checked Step003State.before_binding
  have h := SemanticReplay.forward Step003Rows.certificate Step003State.prior_binding rfl before_binding
  rw [after_binding] at h
  rw [Step003State.state_binding] at h
  exact SemanticReplay.trans (SemanticReplay.verified refineTrace) h
theorem trace : SemanticReplay InitialState.state state :=
  SemanticReplay.trans Step002Trace.trace step_trace

end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step003Trace
