import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf005p0 : QPoint := ((273900168071544029355729369978836519973/236441299765600000000000000000000000000), (1468303/2203874))
def leaf005p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf005p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf005p3 : QPoint := ((1468303/2203874), (6219794695707045443789933404801827773/4912077016475000000000000000000000000))
def leaf005p4 : QPoint := ((1468303/2203874), (1468303/2203874))

def leaf005 : WallOwnershipLeaf where
  margin := (1468303/2203874)
  polygon := [baselineEdge leaf005p0 leaf005p1, baselineEdge leaf005p1 leaf005p2, baselineEdge leaf005p2 leaf005p3, baselineEdge leaf005p3 leaf005p4, baselineEdge leaf005p4 leaf005p0]
  vertices := [leaf005p0, leaf005p1, leaf005p2, leaf005p3, leaf005p4]
  implications := [[(9, (43785574508413808943069800095097811532091939/67668338507422079557887200000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (98745609383864811723768717580092581792021/122213514641924207012700000000000000000000))], [(0, (2947185907944545443789933404801827773/4912077016475000000000000000000000000))], [(2, (116374161698344029355729369978836519973/236441299765600000000000000000000000000))]]

theorem leaf005_checked : leaf005.Check 0 [point] (231/1024) (73/256) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf005, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf005, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf005p0, leaf005p1, leaf005p2, leaf005p3, leaf005p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf005]
      · intro v hv
        simp only [leaf005, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf005p4, by simp [leaf005], leaf005p1, by simp [leaf005],
            by simp [leaf005], by simp [leaf005], ?_⟩
          norm_num [leaf005p4, leaf005p0, leaf005p1]
        · refine ⟨leaf005p0, by simp [leaf005], leaf005p2, by simp [leaf005],
            by simp [leaf005], by simp [leaf005], ?_⟩
          norm_num [leaf005p0, leaf005p1, leaf005p2]
        · refine ⟨leaf005p1, by simp [leaf005], leaf005p3, by simp [leaf005],
            by simp [leaf005], by simp [leaf005], ?_⟩
          norm_num [leaf005p1, leaf005p2, leaf005p3]
        · refine ⟨leaf005p2, by simp [leaf005], leaf005p4, by simp [leaf005],
            by simp [leaf005], by simp [leaf005], ?_⟩
          norm_num [leaf005p2, leaf005p3, leaf005p4]
        · refine ⟨leaf005p3, by simp [leaf005], leaf005p0, by simp [leaf005],
            by simp [leaf005], by simp [leaf005], ?_⟩
          norm_num [leaf005p3, leaf005p4, leaf005p0]
    · intro v hv
      simp only [leaf005, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf005, point, leaf005p0, leaf005p1, leaf005p2, leaf005p3, leaf005p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
