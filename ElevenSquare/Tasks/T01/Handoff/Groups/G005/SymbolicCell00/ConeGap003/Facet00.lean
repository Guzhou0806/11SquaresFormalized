import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem witness00_checked :
    (witness00).Check source facet00 left right := by
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
    baselineRationalCap, witness00, facet00, left, right]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap003.witness00_checked
