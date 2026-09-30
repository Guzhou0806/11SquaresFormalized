import ElevenSquare.Tasks.T01.WallSeedRoot
namespace ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row003
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
/-- Source seed SHA256 36a0635058caa12d6e2e640999e800fa932d522bae98f17b2d757930fcf4c611, physical cell 1,
    archived interval [(3/32), (1/8)]. -/
def p0 : QPoint := ((433243950439915018992474462316632743/215210674800000000000000000000000000), (1207/2066))
def p1 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def p2 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def p3 : QPoint := ((250840128175618916802383837903744157/221649570400000000000000000000000000), (1207/2066))
def vertices : List QPoint := [p0, p1, p2, p3]
def polygon : Polygon := [
  baselineEdge p0 p1,
  baselineEdge p1 p2,
  baselineEdge p2 p3,
  baselineEdge p3 p0
]
def witnesses : List BaselineCombination := [
  [(10, (6255943645952935493952636040734569654353/7514600352903302541300000000000000000000))],
  [(13, (3505336102483440021987746380675713106987011/3197821607768971947957040000000000000000000))],
  [(8, (50745290221174864202028885043551527276651/63435018225331401144800000000000000000000))],
  [(2, (101754264864018913309544340274864566277823/115443740597565600000000000000000000000000))]
]
def margin : ℚ := (1207/2066)
theorem wall_checked : BaselineWallCheck (3/32) (1/8) margin := by
  norm_num [BaselineWallCheck, margin]
theorem domain_checked :
    BaselinePolygonImplicationCheck (baselineSlab 1 margin) polygon witnesses := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, polygon, witnesses, margin,
    baselineEdge, List.getD, List.finRange, p0, p1, p2, p3]
end
end ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row003
#print axioms ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row003.wall_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row003.domain_checked
