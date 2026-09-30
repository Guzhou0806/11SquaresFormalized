import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime003.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem witness04_checked :
    (witness04).Check source facet04 left right := by
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
    baselineRationalCap, witness04, facet04, left, right]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime003

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell00.Regime003.witness04_checked
