import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.Leaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.Leaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem node000_checked :
    node000.Check nodeSource000 targets left right := by
  have hl : splitFacet000 :: nodeSource000 = nodeSource001 := by
    norm_num [splitFacet000, nodeSource000, nodeSource001]
  have hr : splitFacet000.flip :: nodeSource000 = nodeSource002 := by
    norm_num [splitFacet000, nodeSource000, nodeSource002,
      SymbolicFacet.flip, SymbolicQuadratic.neg]
  simpa [node000, SymbolicCoverCertificate.Check, hl, hr] using
    (show node001.Check nodeSource001 targets left right ∧
      node002.Check nodeSource002 targets left right from
      ⟨node001_checked, node002_checked⟩)

theorem cover_checked : node000.Check source targets left right := by
  simpa [nodeSource000, source] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000
