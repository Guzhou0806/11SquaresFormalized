import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.Cached.Leaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.Cached.Leaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem node000_checked :
    SymbolicCoverSignRefs.Check cache nodeSource000 targets
      left right node000 signNode000 := by
  have hl : splitFacet000 :: nodeSource000 = nodeSource001 := by
    norm_num [splitFacet000, nodeSource000, nodeSource001]
  have hr : splitFacet000.flip :: nodeSource000 = nodeSource002 := by
    norm_num [splitFacet000, nodeSource000, nodeSource002,
      SymbolicFacet.flip, SymbolicQuadratic.neg]
  simpa [node000, signNode000, SymbolicCoverSignRefs.Check, hl, hr] using
    (show SymbolicCoverSignRefs.Check cache nodeSource001 targets
       left right node001 signNode001 ∧
      SymbolicCoverSignRefs.Check cache nodeSource002 targets
       left right node002 signNode002 from
      ⟨node001_checked, node002_checked⟩)

theorem cover_checked : SymbolicCoverSignRefs.Check cache
    source targets left right node000 signNode000 := by
  simpa [nodeSource000, source] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.Cached
