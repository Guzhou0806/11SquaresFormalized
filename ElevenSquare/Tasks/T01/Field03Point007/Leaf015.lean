import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf015p0 : QPoint := ((1937730118215826029383017169184524101917/1747120660642400000000000000000000000000), (8384887/16284946))
def leaf015p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf015p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf015p3 : QPoint := ((8384887/16284946), (45920497923631345018664905906959248117/36296498330275000000000000000000000000))
def leaf015p4 : QPoint := ((8384887/16284946), (8384887/16284946))

def leaf015 : WallOwnershipLeaf where
  margin := (8384887/16284946)
  polygon := [baselineEdge leaf015p0 leaf015p1, baselineEdge leaf015p1 leaf015p2, baselineEdge leaf015p2 leaf015p3, baselineEdge leaf015p3 leaf015p4, baselineEdge leaf015p4 leaf015p0]
  vertices := [leaf015p0, leaf015p1, leaf015p2, leaf015p3, leaf015p4]
  implications := [[(9, (464621886199022536282368578593632270047332331/500017350584965004718008800000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (985169342048716462439205000957885237306509/903064551972547000098300000000000000000000))], [(0, (27231947344768845018664905906959248117/36296498330275000000000000000000000000))], [(2, (1038162547353026029383017169184524101917/1747120660642400000000000000000000000000))]]

theorem leaf015_checked : leaf015.Check 0 [point] (963/1024) (1987/2048) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf015, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf015, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf015p0, leaf015p1, leaf015p2, leaf015p3, leaf015p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf015]
      · intro v hv
        simp only [leaf015, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf015p4, by simp [leaf015], leaf015p1, by simp [leaf015],
            by simp [leaf015], by simp [leaf015], ?_⟩
          norm_num [leaf015p4, leaf015p0, leaf015p1]
        · refine ⟨leaf015p0, by simp [leaf015], leaf015p2, by simp [leaf015],
            by simp [leaf015], by simp [leaf015], ?_⟩
          norm_num [leaf015p0, leaf015p1, leaf015p2]
        · refine ⟨leaf015p1, by simp [leaf015], leaf015p3, by simp [leaf015],
            by simp [leaf015], by simp [leaf015], ?_⟩
          norm_num [leaf015p1, leaf015p2, leaf015p3]
        · refine ⟨leaf015p2, by simp [leaf015], leaf015p4, by simp [leaf015],
            by simp [leaf015], by simp [leaf015], ?_⟩
          norm_num [leaf015p2, leaf015p3, leaf015p4]
        · refine ⟨leaf015p3, by simp [leaf015], leaf015p0, by simp [leaf015],
            by simp [leaf015], by simp [leaf015], ?_⟩
          norm_num [leaf015p3, leaf015p4, leaf015p0]
    · intro v hv
      simp only [leaf015, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf015, point, leaf015p0, leaf015p1, leaf015p2, leaf015p3, leaf015p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
