import ElevenSquare.Tasks.T01.WallSeedRoot
namespace ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row004
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
/-- Source seed SHA256 36a0635058caa12d6e2e640999e800fa932d522bae98f17b2d757930fcf4c611, physical cell 1,
    archived interval [(1/8), (5/32)]. -/
def p0 : QPoint := ((5429483716591379716265409496724323/2708362800000000000000000000000000), (79/130))
def p1 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def p2 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def p3 : QPoint := ((3178087472181070588994181890366577/2789394400000000000000000000000000), (79/130))
def vertices : List QPoint := [p0, p1, p2, p3]
def polygon : Polygon := [
  baselineEdge p0 p1,
  baselineEdge p1 p2,
  baselineEdge p2 p3,
  baselineEdge p3 p0
]
def witnesses : List BaselineCombination := [
  [(10, (74467453792646351811601421616214332533/94569026706430719300000000000000000000))],
  [(13, (3505336102483440021987746380675713106987011/3197821607768971947957040000000000000000000))],
  [(8, (603683733035818271661544535882061814711/798310974762157032800000000000000000000))],
  [(2, (1257222613298064465657382791455217194203/1452825389901600000000000000000000000000))]
]
def margin : ℚ := (79/130)
theorem wall_checked : BaselineWallCheck (1/8) (5/32) margin := by
  norm_num [BaselineWallCheck, margin]
theorem domain_checked :
    BaselinePolygonImplicationCheck (baselineSlab 1 margin) polygon witnesses := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, polygon, witnesses, margin,
    baselineEdge, List.getD, List.finRange, p0, p1, p2, p3]
end
end ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row004
#print axioms ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row004.wall_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row004.domain_checked
