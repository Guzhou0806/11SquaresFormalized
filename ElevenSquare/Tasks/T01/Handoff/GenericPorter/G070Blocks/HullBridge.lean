import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Blocks.Terminal
import ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step06
import ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression.Step07

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070CoarseTerminal
open ElevenSquare.Tasks.T01.Handoff.Groups.G070.OwnershipCompression

theorem k10_matches : Step06.output = G070Block000.owned1 := by
  norm_num [Step06.output, G070Block000.owned1]

theorem k11_matches : Step07.output = G070Block000.owned0 := by
  norm_num [Step07.output, G070Block000.owned0]

#print axioms k10_matches
#print axioms k11_matches

end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070CoarseTerminal
