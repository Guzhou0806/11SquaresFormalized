import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf000p0 : QPoint := ((425686698199336901251185345901871/208335600000000000000000000000000), (1/2))
def leaf000p1 : QPoint := ((1207374739114251067047341103669/463880000000000000000000000000), (1/2))
def leaf000p2 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf000p3 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf000p4 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf000p5 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))

def leaf000 : WallOwnershipLeaf where
  margin := (1/2)
  polygon := [baselineEdge leaf000p0 leaf000p1, baselineEdge leaf000p1 leaf000p2, baselineEdge leaf000p2 leaf000p3, baselineEdge leaf000p3 leaf000p4, baselineEdge leaf000p4 leaf000p5, baselineEdge leaf000p5 leaf000p0]
  vertices := [leaf000p0, leaf000p1, leaf000p2, leaf000p3, leaf000p4, leaf000p5]
  implications := [[(2, (1351789878437564071288704474514584923/2416067953200000000000000000000000000))], [(11, (1461007499885373359708830921452652159/1018452612643737600000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (7232400458038950139353955508939564041/7274540515879286100000000000000000000))]]

theorem leaf000_polygon_checked : BaselinePolygonCheck leaf000.vertices leaf000.polygon := by
  constructor
  · simp [leaf000]
  · intro v hv
    simp only [leaf000, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf000p5, by simp [leaf000], leaf000p1, by simp [leaf000],
        by simp [leaf000], by simp [leaf000], ?_⟩
      norm_num [leaf000p5, leaf000p0, leaf000p1]
    · refine ⟨leaf000p0, by simp [leaf000], leaf000p2, by simp [leaf000],
        by simp [leaf000], by simp [leaf000], ?_⟩
      norm_num [leaf000p0, leaf000p1, leaf000p2]
    · refine ⟨leaf000p1, by simp [leaf000], leaf000p3, by simp [leaf000],
        by simp [leaf000], by simp [leaf000], ?_⟩
      norm_num [leaf000p1, leaf000p2, leaf000p3]
    · refine ⟨leaf000p2, by simp [leaf000], leaf000p4, by simp [leaf000],
        by simp [leaf000], by simp [leaf000], ?_⟩
      norm_num [leaf000p2, leaf000p3, leaf000p4]
    · refine ⟨leaf000p3, by simp [leaf000], leaf000p5, by simp [leaf000],
        by simp [leaf000], by simp [leaf000], ?_⟩
      norm_num [leaf000p3, leaf000p4, leaf000p5]
    · refine ⟨leaf000p4, by simp [leaf000], leaf000p0, by simp [leaf000],
        by simp [leaf000], by simp [leaf000], ?_⟩
      norm_num [leaf000p4, leaf000p5, leaf000p0]

theorem leaf000_checked : leaf000.Check 2 owned 0 (1/512) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf000, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf000, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf000p0, leaf000p1, leaf000p2, leaf000p3, leaf000p4, leaf000p5]
  · intro p hp
    constructor
    · exact leaf000_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf000, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf000, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf000p0, leaf000p1, leaf000p2, leaf000p3, leaf000p4, leaf000p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
