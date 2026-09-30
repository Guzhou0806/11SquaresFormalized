import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf013p0 : QPoint := ((15796537208485263871615434347697/6030440000000000000000000000000), (79/130))
def leaf013p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf013p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf013p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf013p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf013p5 : QPoint := ((5429483716591379716265409496724323/2708362800000000000000000000000000), (79/130))

def leaf013 : WallOwnershipLeaf where
  margin := (79/130)
  polygon := [baselineEdge leaf013p0 leaf013p1, baselineEdge leaf013p1 leaf013p2, baselineEdge leaf013p2 leaf013p3, baselineEdge leaf013p3 leaf013p4, baselineEdge leaf013p4 leaf013p5, baselineEdge leaf013p5 leaf013p0]
  vertices := [leaf013p0, leaf013p1, leaf013p2, leaf013p3, leaf013p4, leaf013p5]
  implications := [[(11, (15919385207181853676214801978884478067/13239883964368588800000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (74467453792646351811601421616214332533/94569026706430719300000000000000000000))], [(2, (19308803769992332926753158168689603999/31408883391600000000000000000000000000))]]

theorem leaf013_polygon_checked : BaselinePolygonCheck leaf013.vertices leaf013.polygon := by
  constructor
  · simp [leaf013]
  · intro v hv
    simp only [leaf013, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf013p5, by simp [leaf013], leaf013p1, by simp [leaf013],
        by simp [leaf013], by simp [leaf013], ?_⟩
      norm_num [leaf013p5, leaf013p0, leaf013p1]
    · refine ⟨leaf013p0, by simp [leaf013], leaf013p2, by simp [leaf013],
        by simp [leaf013], by simp [leaf013], ?_⟩
      norm_num [leaf013p0, leaf013p1, leaf013p2]
    · refine ⟨leaf013p1, by simp [leaf013], leaf013p3, by simp [leaf013],
        by simp [leaf013], by simp [leaf013], ?_⟩
      norm_num [leaf013p1, leaf013p2, leaf013p3]
    · refine ⟨leaf013p2, by simp [leaf013], leaf013p4, by simp [leaf013],
        by simp [leaf013], by simp [leaf013], ?_⟩
      norm_num [leaf013p2, leaf013p3, leaf013p4]
    · refine ⟨leaf013p3, by simp [leaf013], leaf013p5, by simp [leaf013],
        by simp [leaf013], by simp [leaf013], ?_⟩
      norm_num [leaf013p3, leaf013p4, leaf013p5]
    · refine ⟨leaf013p4, by simp [leaf013], leaf013p0, by simp [leaf013],
        by simp [leaf013], by simp [leaf013], ?_⟩
      norm_num [leaf013p4, leaf013p5, leaf013p0]

theorem leaf013_checked : leaf013.Check 2 owned (1/8) (5/32) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf013, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf013, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf013p0, leaf013p1, leaf013p2, leaf013p3, leaf013p4, leaf013p5]
  · intro p hp
    constructor
    · exact leaf013_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf013, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf013, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf013p0, leaf013p1, leaf013p2, leaf013p3, leaf013p4, leaf013p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
