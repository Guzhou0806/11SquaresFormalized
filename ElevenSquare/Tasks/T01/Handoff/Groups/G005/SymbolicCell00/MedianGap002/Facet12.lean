import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem witness12_checked :
    (witness12).Check source facet12 left right := by
  norm_num [SymbolicFarkasWitness.Check,
    SymbolicFarkasWitness.margin,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.toBernstein, Quartic.shift,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul,
    quarticAdd, quarticSub, List.getD,
    source, symbolicWallScaledSlab, symbolicWallSlab,
    scaledWallFacet, SymbolicQuadratic.scaleByChart,
    SymbolicWallFacet.ofHalfplane, baselineCellPolygon,
    baselineCenterBox, baselineBisector, baselineRationalSite,
    baselineRationalCap, witness12, facet12, left, right]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap002.witness12_checked
