import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem node002_checked :
    node002.Check nodeSource002 targets left right := by
  norm_num [SymbolicCoverCertificate.Check, SymbolicPolygonImplicationCheck, SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin, Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn, Quartic.toBernstein, Quartic.shift, SymbolicQuadratic.quartic, SymbolicQuadratic.mul, quarticAdd, quarticSub, List.getD, targets, source, SymbolicFacet.flip, SymbolicQuadratic.neg, left, right, target00, target01, splitFacet000, node002, nodeSource002]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000
