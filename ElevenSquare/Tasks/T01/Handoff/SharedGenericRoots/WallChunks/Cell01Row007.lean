import ElevenSquare.Tasks.T01.WallSeedRoot
namespace ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section
/-- Source seed SHA256 36a0635058caa12d6e2e640999e800fa932d522bae98f17b2d757930fcf4c611, physical cell 1,
    archived interval [(7/32), (1/4)]. -/
def p0 : QPoint := ((443706407167888495042521876152707583/223544098800000000000000000000000000), (1423/2146))
def p1 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def p2 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def p3 : QPoint := ((266471662797714518614673628335641317/230232322400000000000000000000000000), (1423/2146))
def vertices : List QPoint := [p0, p1, p2, p3]
def polygon : Polygon := [
  baselineEdge p0 p1,
  baselineEdge p1 p2,
  baselineEdge p2 p3,
  baselineEdge p3 p0
]
def witnesses : List BaselineCombination := [
  [(10, (5316146671243293499526794261092152215993/7805581973538473985300000000000000000000))],
  [(13, (3505336102483440021987746380675713106987011/3197821607768971947957040000000000000000000))],
  [(8, (43021847696698735807141329769342486706531/65891359686138038168800000000000000000000))],
  [(2, (99225043965914250126951671940880619183063/119913972566493600000000000000000000000000))]
]
def margin : ℚ := (1423/2146)
theorem wall_checked : BaselineWallCheck (7/32) (1/4) margin := by
  norm_num [BaselineWallCheck, margin]
theorem domain_checked :
    BaselinePolygonImplicationCheck (baselineSlab 1 margin) polygon witnesses := by
  norm_num [BaselinePolygonImplicationCheck, BaselineImplicationCheck,
    BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
    baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, polygon, witnesses, margin,
    baselineEdge, List.getD, List.finRange, p0, p1, p2, p3]
end
end ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row007
#print axioms ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row007.wall_checked
#print axioms ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.WallChunks.Cell01Row007.domain_checked
