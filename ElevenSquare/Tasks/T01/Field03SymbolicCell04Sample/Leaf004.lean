import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.Data

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem node004_checked :
    node004.Check nodeSource004 targets (1/256) (1/128) := by
  norm_num [SymbolicCoverCertificate.Check, SymbolicPolygonImplicationCheck,
    SymbolicFarkasWitness.Check, SymbolicFarkasWitness.margin,
    Quartic.BernsteinPosCheck, Quartic.BernsteinNonnegCheck, Quartic.bernsteinOn,
    Quartic.toBernstein, Quartic.shift, SymbolicQuadratic.quartic,
    SymbolicQuadratic.mul, quarticAdd, quarticSub, List.getD,
    node004, nodeSource004, targets, target01, splitFacet000, source, SymbolicFacet.flip, SymbolicQuadratic.neg]

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
