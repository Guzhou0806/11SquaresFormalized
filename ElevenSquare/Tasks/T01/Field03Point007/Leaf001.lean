import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf001p0 : QPoint := ((162332182902866001631180125866427248421/144544057551200000000000000000000000000), (18785783/33682450))
def leaf001p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf001p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf001p3 : QPoint := ((18785783/33682450), (3800042289408890591897399622856249021/3002908306075000000000000000000000000))
def leaf001p4 : QPoint := ((18785783/33682450), (18785783/33682450))

def leaf001 : WallOwnershipLeaf where
  margin := (18785783/33682450)
  polygon := [baselineEdge leaf001p0 leaf001p1, baselineEdge leaf001p1 leaf001p2, baselineEdge leaf001p2 leaf001p3, baselineEdge leaf001p3 leaf001p4, baselineEdge leaf001p4 leaf001p0]
  vertices := [leaf001p0, leaf001p1, leaf001p2, leaf001p3, leaf001p4]
  implications := [[(9, (35135213533515802444809831927108850724480803/41367799218273255614514400000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (75521356276362807555706971296101127044117/74712993505996803927900000000000000000000))], [(0, (2125223984718390591897399622856249021/3002908306075000000000000000000000000))], [(2, (81715324595458001631180125866427248421/144544057551200000000000000000000000000))]]

theorem leaf001_checked : leaf001.Check 0 [point] (253/4096) (157/2048) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf001, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf001, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf001p0, leaf001p1, leaf001p2, leaf001p3, leaf001p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf001]
      · intro v hv
        simp only [leaf001, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf001p4, by simp [leaf001], leaf001p1, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p4, leaf001p0, leaf001p1]
        · refine ⟨leaf001p0, by simp [leaf001], leaf001p2, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p0, leaf001p1, leaf001p2]
        · refine ⟨leaf001p1, by simp [leaf001], leaf001p3, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p1, leaf001p2, leaf001p3]
        · refine ⟨leaf001p2, by simp [leaf001], leaf001p4, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p2, leaf001p3, leaf001p4]
        · refine ⟨leaf001p3, by simp [leaf001], leaf001p0, by simp [leaf001],
            by simp [leaf001], by simp [leaf001], ?_⟩
          norm_num [leaf001p3, leaf001p4, leaf001p0]
    · intro v hv
      simp only [leaf001, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf001, point, leaf001p0, leaf001p1, leaf001p2, leaf001p3, leaf001p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
