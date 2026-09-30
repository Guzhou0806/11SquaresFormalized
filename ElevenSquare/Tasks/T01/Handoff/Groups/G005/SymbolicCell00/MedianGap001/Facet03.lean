import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap001.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem witness03_checked :
    (witness03).Check source facet03 left right := by
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
    baselineRationalCap, witness03, facet03, left, right]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap001

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.MedianGap001.witness03_checked
