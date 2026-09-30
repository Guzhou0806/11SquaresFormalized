import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf007p0 : QPoint := ((49591525263684293748940985250429/19019080000000000000000000000000), (1087/2050))
def leaf007p1 : QPoint := ((353623643836430097391319046894515449/130685046400000000000000000000000000), (2558761889645373359708830921452652159/2195508779520000000000000000000000000))
def leaf007p2 : QPoint := ((42291650516791725682418373348708388223/16230123890800000000000000000000000000), (147287171458817317141943162616562655337/113610867235600000000000000000000000000))
def leaf007p3 : QPoint := ((11951832558217502702915582678034857457/5844631653800000000000000000000000000), (7596420311416457308245524933208538003/5844631653800000000000000000000000000))
def leaf007p4 : QPoint := ((20758803146700947451083028546721467951/11173572663920000000000000000000000000), (14215883372988950139353955508939564041/13966965829900000000000000000000000000))
def leaf007p5 : QPoint := ((17360647650172812951298599181976711/8541759600000000000000000000000000), (1087/2050))

def leaf007 : WallOwnershipLeaf where
  margin := (1087/2050)
  polygon := [baselineEdge leaf007p0 leaf007p1, baselineEdge leaf007p1 leaf007p2, baselineEdge leaf007p2 leaf007p3, baselineEdge leaf007p3 leaf007p4, baselineEdge leaf007p4 leaf007p5, baselineEdge leaf007p5 leaf007p0]
  vertices := [leaf007p0, leaf007p1, leaf007p2, leaf007p3, leaf007p4, leaf007p5]
  implications := [[(11, (57178876608695507748062067779558738519/41756557118393241600000000000000000000))], [(15, (113377395977525955769531074834195112760203/445417243686858771955200000000000000000000))], [(14, (3357742218402206280316909943964905309691911/3320068354304285311176400000000000000000000))], [(13, (1753548343070084977915564592132090647446583/3265270823879061059544800000000000000000000))], [(9, (279209381150520955713512175866522125681/298256161151050730100000000000000000000))], [(2, (56960573469066526922836883455097981843/99058786081200000000000000000000000000))]]

theorem leaf007_polygon_checked : BaselinePolygonCheck leaf007.vertices leaf007.polygon := by
  constructor
  · simp [leaf007]
  · intro v hv
    simp only [leaf007, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨leaf007p5, by simp [leaf007], leaf007p1, by simp [leaf007],
        by simp [leaf007], by simp [leaf007], ?_⟩
      norm_num [leaf007p5, leaf007p0, leaf007p1]
    · refine ⟨leaf007p0, by simp [leaf007], leaf007p2, by simp [leaf007],
        by simp [leaf007], by simp [leaf007], ?_⟩
      norm_num [leaf007p0, leaf007p1, leaf007p2]
    · refine ⟨leaf007p1, by simp [leaf007], leaf007p3, by simp [leaf007],
        by simp [leaf007], by simp [leaf007], ?_⟩
      norm_num [leaf007p1, leaf007p2, leaf007p3]
    · refine ⟨leaf007p2, by simp [leaf007], leaf007p4, by simp [leaf007],
        by simp [leaf007], by simp [leaf007], ?_⟩
      norm_num [leaf007p2, leaf007p3, leaf007p4]
    · refine ⟨leaf007p3, by simp [leaf007], leaf007p5, by simp [leaf007],
        by simp [leaf007], by simp [leaf007], ?_⟩
      norm_num [leaf007p3, leaf007p4, leaf007p5]
    · refine ⟨leaf007p4, by simp [leaf007], leaf007p0, by simp [leaf007],
        by simp [leaf007], by simp [leaf007], ?_⟩
      norm_num [leaf007p4, leaf007p5, leaf007p0]

theorem leaf007_checked : leaf007.Check 2 owned (1/32) (5/128) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf007, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf007, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf007p0, leaf007p1, leaf007p2, leaf007p3, leaf007p4, leaf007p5]
  · intro p hp
    constructor
    · exact leaf007_polygon_checked
    · simp only [owned, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals intro v hv
      all_goals simp only [leaf007, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf007, ownedP005, ownedP006, ownedP007, ownedP008, ownedP009, leaf007p0, leaf007p1, leaf007p2, leaf007p3, leaf007p4, leaf007p5, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell02Group
