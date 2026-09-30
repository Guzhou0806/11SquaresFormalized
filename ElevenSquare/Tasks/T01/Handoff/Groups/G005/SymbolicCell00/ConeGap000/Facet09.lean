import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem witness09_checked :
    (witness09).Check source facet09 left right := by
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
    baselineRationalCap, witness09, facet09, left, right]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.ConeGap000.witness09_checked
