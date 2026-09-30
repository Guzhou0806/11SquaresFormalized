import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf008p0 : QPoint := ((19856033054125745759179820170104621/7611806920000000000000000000000000), (17639/32818))
def leaf008p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf008p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf008p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf008p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf008p5 : QPoint := ((6939212554752919212630700340903801239/3418578860400000000000000000000000000), (17639/32818))

def leaf008 : WallOwnershipLeaf where
  margin := (17639/32818)
  polygon := [baselineEdge leaf008p0 leaf008p1, baselineEdge leaf008p1 leaf008p2, baselineEdge leaf008p2 leaf008p3, baselineEdge leaf008p3 leaf008p4, baselineEdge leaf008p4 leaf008p5, baselineEdge leaf008p5 leaf008p0]
  vertices := [leaf008p0, leaf008p1, leaf008p2, leaf008p3, leaf008p4, leaf008p5]
  implications := [[(11, (22623434166214291459462206590116569277031/16711788920871090278400000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (110086775130572632836659055946189306348769/119367935325063205614900000000000000000000))], [(2, (22943916001308388845776351722309824001507/39645259044058800000000000000000000000000))]]

theorem leaf008_polygon_checked : BaselinePolygonCheck leaf008.vertices leaf008.polygon := by
  constructor
  · simp [leaf008]
  · intro v hv
    simp only [leaf008, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf008p5, by simp [leaf008], leaf008p1, by simp [leaf008],
        by simp [leaf008], by simp [leaf008], ?_⟩
      norm_num [leaf008p5, leaf008p0, leaf008p1]
    · refine ⟨leaf008p0, by simp [leaf008], leaf008p2, by simp [leaf008],
        by simp [leaf008], by simp [leaf008], ?_⟩
      norm_num [leaf008p0, leaf008p1, leaf008p2]
    · refine ⟨leaf008p1, by simp [leaf008], leaf008p3, by simp [leaf008],
        by simp [leaf008], by simp [leaf008], ?_⟩
      norm_num [leaf008p1, leaf008p2, leaf008p3]
    · refine ⟨leaf008p2, by simp [leaf008], leaf008p4, by simp [leaf008],
        by simp [leaf008], by simp [leaf008], ?_⟩
      norm_num [leaf008p2, leaf008p3, leaf008p4]
    · refine ⟨leaf008p3, by simp [leaf008], leaf008p5, by simp [leaf008],
        by simp [leaf008], by simp [leaf008], ?_⟩
      norm_num [leaf008p3, leaf008p4, leaf008p5]
    · refine ⟨leaf008p4, by simp [leaf008], leaf008p0, by simp [leaf008],
        by simp [leaf008], by simp [leaf008], ?_⟩
      norm_num [leaf008p4, leaf008p5, leaf008p0]

theorem leaf008_checked : leaf008.Check 2 owned (5/128) (3/64) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf008, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf008, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf008p0, leaf008p1, leaf008p2, leaf008p3, leaf008p4, leaf008p5]
  · intro p hp
    constructor
    · exact leaf008_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf008, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf008, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf008p0, leaf008p1, leaf008p2, leaf008p3, leaf008p4, leaf008p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
