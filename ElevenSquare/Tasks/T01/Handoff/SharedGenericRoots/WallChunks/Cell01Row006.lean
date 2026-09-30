import ElevenSquare.Tasks.T01.WallSeedRoot
namespace ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row006
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
/-- Source seed SHA256 36a0635058caa12d6e2e640999e800fa932d522bae98f17b2d757930fcf4c611, physical cell 1,
    archived interval [(3/16), (7/32)]. -/
def p0 : QPoint := ((21979496284564855766312823332799163/11041786800000000000000000000000000), (343/530))
def p1 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def p2 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def p3 : QPoint := ((13103138254276672401283972322263737/11372146400000000000000000000000000), (343/530))
def vertices : List QPoint := [p0, p1, p2, p3]
def polygon : Polygon := [
  baselineEdge p0 p1,
  baselineEdge p1 p2,
  baselineEdge p2 p3,
  baselineEdge p3 p0
]
def witnesses : List BaselineCombination := [
  [(10, (274374890802844357385759641973796894173/385550647341602163300000000000000000000))],
  [(13, (3505336102483440021987746380675713106987011/3197821607768971947957040000000000000000000))],
  [(8, (2221648869031369876773989261673021244591/3254652435568794056800000000000000000000))],
  [(2, (4965659930739641283064714457471270099443/5923057358829600000000000000000000000000))]
]
def margin : ℚ := (343/530)
theorem wall_checked : BaselineWallCheck (3/16) (7/32) margin := by
  norm_num [BaselineWallCheck, margin]
theorem domain_checked :
    BaselinePolygonImplicationCheck (baselineSlab 1 margin) polygon witnesses := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, polygon, witnesses, margin,
    baselineEdge, List.getD, List.finRange, p0, p1, p2, p3]
end
end ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row006
#print axioms ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row006.wall_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row006.domain_checked
