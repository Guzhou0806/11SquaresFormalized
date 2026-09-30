import ElevenSquare.Tasks.T01.Handoff.Groups.G000.FeatureData
import ElevenSquare.Tasks.T01.Handoff.Groups.G001.FeatureData

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G001

/-- Both archived packets use the same five physical sites for their first feature. -/
theorem featureA_eq_G000 : featureA = G000.featureA := by
  rfl

end ElevenSquare.Tasks.T01.Handoff.Groups.G001

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G001.featureA_eq_G000
