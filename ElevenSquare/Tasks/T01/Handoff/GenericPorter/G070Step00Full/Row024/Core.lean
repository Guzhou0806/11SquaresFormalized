import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full.Row024.Data
namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full.Row024
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 0
theorem core_checked :
    ∀ v ∈ core, BaselineCoreVertexCheck v sourceRow.lo sourceRow.hi := by
  norm_num [core, sourceRow, BaselineCoreVertexCheck, BaselineQuadraticCheck]
#print axioms core_checked
end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full.Row024
