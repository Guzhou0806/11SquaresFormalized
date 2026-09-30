import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012.Data

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem node002_checked :
    node002.Check nodeSource002 targets (1923/2048) (4069/4096) := by
  norm_num [SymbolicCoverCertificate.Check, SymbolicPolygonImplicationCheck,
    SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.toBernstein, Quartic.shift,
    SymbolicQuadratic.quartic, SymbolicQuadratic.mul, quarticAdd,
    quarticSub, List.getD, node002, nodeSource002, targets, target00, target01, splitFacet000, splitFacet001, source, SymbolicFacet.flip, SymbolicQuadratic.neg]

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime012
