import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf009p0 : QPoint := ((993886347212800126045867046112249/380845480000000000000000000000000), (4471/8210))
def leaf009p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf009p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf009p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf009p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf009p5 : QPoint := ((346758331381655595927223168985436091/171043527600000000000000000000000000), (4471/8210))

def leaf009 : WallOwnershipLeaf where
  margin := (4471/8210)
  polygon := [baselineEdge leaf009p0 leaf009p1, baselineEdge leaf009p1 leaf009p2, baselineEdge leaf009p2 leaf009p3, baselineEdge leaf009p3 leaf009p4, baselineEdge leaf009p4 leaf009p5, baselineEdge leaf009p5 leaf009p0]
  vertices := [leaf009p0, leaf009p1, leaf009p2, leaf009p3, leaf009p4, leaf009p5]
  implications := [[(11, (1119131536075459528320950186512627422539/836149594980508569600000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (5426609826675638064409597472839382077661/5972397763536893888100000000000000000000))], [(2, (1155191342926616102528026373576474221783/1983591789577200000000000000000000000000))]]

theorem leaf009_polygon_checked : BaselinePolygonCheck leaf009.vertices leaf009.polygon := by
  constructor
  · simp [leaf009]
  · intro v hv
    simp only [leaf009, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf009p5, by simp [leaf009], leaf009p1, by simp [leaf009],
        by simp [leaf009], by simp [leaf009], ?_⟩
      norm_num [leaf009p5, leaf009p0, leaf009p1]
    · refine ⟨leaf009p0, by simp [leaf009], leaf009p2, by simp [leaf009],
        by simp [leaf009], by simp [leaf009], ?_⟩
      norm_num [leaf009p0, leaf009p1, leaf009p2]
    · refine ⟨leaf009p1, by simp [leaf009], leaf009p3, by simp [leaf009],
        by simp [leaf009], by simp [leaf009], ?_⟩
      norm_num [leaf009p1, leaf009p2, leaf009p3]
    · refine ⟨leaf009p2, by simp [leaf009], leaf009p4, by simp [leaf009],
        by simp [leaf009], by simp [leaf009], ?_⟩
      norm_num [leaf009p2, leaf009p3, leaf009p4]
    · refine ⟨leaf009p3, by simp [leaf009], leaf009p5, by simp [leaf009],
        by simp [leaf009], by simp [leaf009], ?_⟩
      norm_num [leaf009p3, leaf009p4, leaf009p5]
    · refine ⟨leaf009p4, by simp [leaf009], leaf009p0, by simp [leaf009],
        by simp [leaf009], by simp [leaf009], ?_⟩
      norm_num [leaf009p4, leaf009p5, leaf009p0]

theorem leaf009_checked : leaf009.Check 2 owned (3/64) (1/16) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf009, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf009, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf009p0, leaf009p1, leaf009p2, leaf009p3, leaf009p4, leaf009p5]
  · intro p hp
    constructor
    · exact leaf009_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf009, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf009, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf009p0, leaf009p1, leaf009p2, leaf009p3, leaf009p4, leaf009p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
