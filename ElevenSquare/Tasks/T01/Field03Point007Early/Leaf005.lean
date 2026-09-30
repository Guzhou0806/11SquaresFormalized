import ElevenSquare.Tasks.T01.Field03Point007Early.Data

namespace ElevenSquare.Tasks.T01.Field03Point007Early
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf005p0 : QPoint := ((3910334293460330012721663363752253597/3517426338400000000000000000000000000), (17143/32786))
def leaf005p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf005p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf005p3 : QPoint := ((17143/32786), (92454528648547417828830848138247797/73074666275000000000000000000000000))
def leaf005p4 : QPoint := ((17143/32786), (17143/32786))

def leaf005 : WallOwnershipLeaf where
  margin := (17143/32786)
  polygon := [baselineEdge leaf005p0 leaf005p1, baselineEdge leaf005p1 leaf005p2, baselineEdge leaf005p2 leaf005p3, baselineEdge leaf005p3 leaf005p4, baselineEdge leaf005p4 leaf005p0]
  vertices := [leaf005p0, leaf005p1, leaf005p2, leaf005p3, leaf005p4]
  implications := [[(9, (9488819044312997531600078966466803591243/10378042671908041426400000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (1956256051407382448350260121304990841869/1818113145783346530300000000000000000000))], [(0, (54245567386047417828830848138247797/73074666275000000000000000000000000))], [(2, (2071157824260330012721663363752253597/3517426338400000000000000000000000000))]]

theorem leaf005_checked : leaf005.Check 0 [point] (3/128) (9/256) := by
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
end ElevenSquare.Tasks.T01.Field03Point007Early
