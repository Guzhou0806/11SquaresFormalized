import ElevenSquare.Tasks.T01.WallSeedRoot
namespace ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row002
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
/-- Source seed SHA256 36a0635058caa12d6e2e640999e800fa932d522bae98f17b2d757930fcf4c611, physical cell 1,
    archived interval [(1/16), (3/32)]. -/
def p0 : QPoint := ((108282445437229583621554633896780847/53542249200000000000000000000000000), (287/514))
def p1 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def p2 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def p3 : QPoint := ((61941816986964241643961903524939253/55144181600000000000000000000000000), (287/514))
def vertices : List QPoint := [p0, p1, p2, p3]
def polygon : Polygon := [
  baselineEdge p0 p1,
  baselineEdge p1 p2,
  baselineEdge p2 p3,
  baselineEdge p3 p0
]
def witnesses : List BaselineCombination := [
  [(10, (1649222430267510185813966565797467958537/1869556912580976527700000000000000000000))],
  [(13, (3505336102483440021987746380675713106987011/3197821607768971947957040000000000000000000))],
  [(8, (13385592274402795062847457363206914336979/15781993885682642879200000000000000000000))],
  [(2, (25823371928656099051842105954153139916167/28721240400362400000000000000000000000000))]
]
def margin : ℚ := (287/514)
theorem wall_checked : BaselineWallCheck (1/16) (3/32) margin := by
  norm_num [BaselineWallCheck, margin]
theorem domain_checked :
    BaselinePolygonImplicationCheck (baselineSlab 1 margin) polygon witnesses := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, polygon, witnesses, margin,
    baselineEdge, List.getD, List.finRange, p0, p1, p2, p3]
end
end ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row002
#print axioms ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row002.wall_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row002.domain_checked
