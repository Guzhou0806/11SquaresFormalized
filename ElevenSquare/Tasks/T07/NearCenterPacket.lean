import ElevenSquare.Tasks.T07.NearCenterBoxData0
import ElevenSquare.Tasks.T07.NearCenterBoxData1
import ElevenSquare.Tasks.T07.NearCenterBoxData2
import ElevenSquare.Tasks.T07.NearCenterBoxData3
import ElevenSquare.Tasks.T07.NearCenterBoxData4
import ElevenSquare.Tasks.T07.NearCenterBoxData5
import ElevenSquare.Tasks.T07.NearCenterBoxData6
import ElevenSquare.Tasks.T07.NearCenterBoxData7
import ElevenSquare.Tasks.T07.NearCenterBoxData8
import ElevenSquare.Tasks.T07.NearCenterBoxData9
import ElevenSquare.Tasks.T07.NearCenterBoxData10
import Mathlib.Tactic.FinCases

/-! Complete final-near center enclosure for all 11 owner roles. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem finalNear_centers_in_focused_radii (i : Owner) (p : Point)
    (hp : InFinalNearCenter i p) :
    |(fieldToLocal p).1-(constructionCenter i).1| ≤ focusedRadii (coordinate i (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter i).2| ≤ focusedRadii (coordinate i (1 : Fin 3)) := by
  fin_cases i
  · exact finalNear_center_role0 p hp
  · exact finalNear_center_role1 p hp
  · exact finalNear_center_role2 p hp
  · exact finalNear_center_role3 p hp
  · exact finalNear_center_role4 p hp
  · exact finalNear_center_role5 p hp
  · exact finalNear_center_role6 p hp
  · exact finalNear_center_role7 p hp
  · exact finalNear_center_role8 p hp
  · exact finalNear_center_role9 p hp
  · exact finalNear_center_role10 p hp

end
end ElevenSquare.Tasks.T07
