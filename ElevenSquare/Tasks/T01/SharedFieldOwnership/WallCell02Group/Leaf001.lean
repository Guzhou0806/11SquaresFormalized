import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf001p0 : QPoint := ((63308798785821069194225046724262001/24320764520000000000000000000000000), (263167/524290))
def leaf001p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf001p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf001p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf001p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf001p5 : QPoint := ((22310703534613034395698396500289194659/10922827172400000000000000000000000000), (263167/524290))

def leaf001 : WallOwnershipLeaf where
  margin := (263167/524290)
  polygon := [baselineEdge leaf001p0 leaf001p1, baselineEdge leaf001p1 leaf001p2, baselineEdge leaf001p2 leaf001p3, baselineEdge leaf001p3 leaf001p4, baselineEdge leaf001p4 leaf001p5, baselineEdge leaf001p5 leaf001p0]
  vertices := [leaf001p0, leaf001p1, leaf001p2, leaf001p3, leaf001p4, leaf001p5]
  implications := [[(11, (76374781214223295876174296380841100044211/53396452028298518630400000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (377760099706708336856188533378192403105589/381396884707035090936900000000000000000000))], [(2, (70999685617175238693595486894325172927967/126672026718322800000000000000000000000000))]]

theorem leaf001_polygon_checked : BaselinePolygonCheck leaf001.vertices leaf001.polygon := by
  constructor
  · simp [leaf001]
  · intro v hv
    simp only [leaf001, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf001p5, by simp [leaf001], leaf001p1, by simp [leaf001],
        by simp [leaf001], by simp [leaf001], ?_⟩
      norm_num [leaf001p5, leaf001p0, leaf001p1]
    · refine ⟨leaf001p0, by simp [leaf001], leaf001p2, by simp [leaf001],
        by simp [leaf001], by simp [leaf001], ?_⟩
      norm_num [leaf001p0, leaf001p1, leaf001p2]
    · refine ⟨leaf001p1, by simp [leaf001], leaf001p3, by simp [leaf001],
        by simp [leaf001], by simp [leaf001], ?_⟩
      norm_num [leaf001p1, leaf001p2, leaf001p3]
    · refine ⟨leaf001p2, by simp [leaf001], leaf001p4, by simp [leaf001],
        by simp [leaf001], by simp [leaf001], ?_⟩
      norm_num [leaf001p2, leaf001p3, leaf001p4]
    · refine ⟨leaf001p3, by simp [leaf001], leaf001p5, by simp [leaf001],
        by simp [leaf001], by simp [leaf001], ?_⟩
      norm_num [leaf001p3, leaf001p4, leaf001p5]
    · refine ⟨leaf001p4, by simp [leaf001], leaf001p0, by simp [leaf001],
        by simp [leaf001], by simp [leaf001], ?_⟩
      norm_num [leaf001p4, leaf001p5, leaf001p0]

theorem leaf001_checked : leaf001.Check 2 owned (1/512) (1/256) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf001, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf001, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf001p0, leaf001p1, leaf001p2, leaf001p3, leaf001p4, leaf001p5]
  · intro p hp
    constructor
    · exact leaf001_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf001, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf001, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf001p0, leaf001p1, leaf001p2, leaf001p3, leaf001p4, leaf001p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
