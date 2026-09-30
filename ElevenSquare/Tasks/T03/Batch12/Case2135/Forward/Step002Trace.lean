import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step001Trace
import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step002Rows
import ElevenSquare.Tasks.T03.SemanticCertificate

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Trace
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Data
noncomputable def state : PoseState := Step002State.state
theorem before_binding : Step002State.refined.rows owner = Step002Rows.certificate.before := by rfl
theorem after_binding : Step002Rows.certificate.after = Step002State.afterRows := by rfl
theorem step_trace : SemanticReplay Step001Trace.state state := by
  have refineTrace := RefinementRows.trace Step002State.before owner Step002State.entries
    Step002State.partition_checked Step002State.before_binding
  have h := SemanticReplay.forward Step002Rows.certificate Step002State.prior_binding rfl before_binding
  rw [after_binding] at h
  rw [Step002State.state_binding] at h
  exact SemanticReplay.trans (SemanticReplay.verified refineTrace) h
theorem trace : SemanticReplay InitialState.state state :=
  SemanticReplay.trans Step001Trace.trace step_trace

end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Trace
