import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step000Trace
import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step001Rows
import ElevenSquare.Tasks.T03.SemanticCertificate

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step001Trace
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step001Data
noncomputable def state : PoseState := Step001State.state
theorem before_binding : Step001State.refined.rows owner = Step001Rows.certificate.before := by rfl
theorem after_binding : Step001Rows.certificate.after = Step001State.afterRows := by rfl
theorem step_trace : SemanticReplay Step000Trace.state state := by
  have refineTrace := RefinementRows.trace Step001State.before owner Step001State.entries
    Step001State.partition_checked Step001State.before_binding
  have h := SemanticReplay.forward Step001Rows.certificate Step001State.prior_binding rfl before_binding
  rw [after_binding] at h
  rw [Step001State.state_binding] at h
  exact SemanticReplay.trans (SemanticReplay.verified refineTrace) h
theorem trace : SemanticReplay InitialState.state state :=
  SemanticReplay.trans Step000Trace.trace step_trace

end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step001Trace
