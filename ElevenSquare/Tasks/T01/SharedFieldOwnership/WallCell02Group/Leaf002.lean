import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf002p0 : QPoint := ((79146053797330672181081593911155253/30401303560000000000000000000000000), (66047/131074))
def leaf002p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf002p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf002p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf002p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf002p5 : QPoint := ((27879205527889942497298934014370919727/13653690217200000000000000000000000000), (66047/131074))

def leaf002 : WallOwnershipLeaf where
  margin := (66047/131074)
  polygon := [baselineEdge leaf002p0 leaf002p1, baselineEdge leaf002p1 leaf002p2, baselineEdge leaf002p2 leaf002p3, baselineEdge leaf002p3 leaf002p4, baselineEdge leaf002p4 leaf002p5, baselineEdge leaf002p5 leaf002p0]
  vertices := [leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4, leaf002p5]
  implications := [[(11, (95190193781210113875237652099242464544383/66746328874832631091200000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (470428252531874175282840182189372208555017/476751561789180773135700000000000000000000))], [(2, (88908368630539436540047825146262352098651/158341845448868400000000000000000000000000))]]

theorem leaf002_polygon_checked : BaselinePolygonCheck leaf002.vertices leaf002.polygon := by
  constructor
  · simp [leaf002]
  · intro v hv
    simp only [leaf002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf002p5, by simp [leaf002], leaf002p1, by simp [leaf002],
        by simp [leaf002], by simp [leaf002], ?_⟩
      norm_num [leaf002p5, leaf002p0, leaf002p1]
    · refine ⟨leaf002p0, by simp [leaf002], leaf002p2, by simp [leaf002],
        by simp [leaf002], by simp [leaf002], ?_⟩
      norm_num [leaf002p0, leaf002p1, leaf002p2]
    · refine ⟨leaf002p1, by simp [leaf002], leaf002p3, by simp [leaf002],
        by simp [leaf002], by simp [leaf002], ?_⟩
      norm_num [leaf002p1, leaf002p2, leaf002p3]
    · refine ⟨leaf002p2, by simp [leaf002], leaf002p4, by simp [leaf002],
        by simp [leaf002], by simp [leaf002], ?_⟩
      norm_num [leaf002p2, leaf002p3, leaf002p4]
    · refine ⟨leaf002p3, by simp [leaf002], leaf002p5, by simp [leaf002],
        by simp [leaf002], by simp [leaf002], ?_⟩
      norm_num [leaf002p3, leaf002p4, leaf002p5]
    · refine ⟨leaf002p4, by simp [leaf002], leaf002p0, by simp [leaf002],
        by simp [leaf002], by simp [leaf002], ?_⟩
      norm_num [leaf002p4, leaf002p5, leaf002p0]

theorem leaf002_checked : leaf002.Check 2 owned (1/256) (1/128) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf002, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf002, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4, leaf002p5]
  · intro p hp
    constructor
    · exact leaf002_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf002, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4, leaf002p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
