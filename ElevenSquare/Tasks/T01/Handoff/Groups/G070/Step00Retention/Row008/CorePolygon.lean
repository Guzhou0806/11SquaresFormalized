import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full.Row008.FreshCoreData
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.RetainedCoreFresh

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G070.Step00Retention.Row008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full.Row008
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 8192

theorem core_polygon_checked : BaselinePolygonCheck core corePolygon := by
  norm_num [BaselinePolygonCheck, core, corePolygon, baselineEdge]

#print axioms core_polygon_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G070.Step00Retention.Row008
