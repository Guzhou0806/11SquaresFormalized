import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf002p0 : QPoint := ((1020388448341312638819136205300595471837/905255682466400000000000000000000000000), (4812727/8437906))
def leaf002p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf002p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf002p3 : QPoint := ((4812727/8437906), (23800729324522166418056450512133530037/18806721314275000000000000000000000000))
def leaf002p4 : QPoint := ((4812727/8437906), (4812727/8437906))

def leaf002 : WallOwnershipLeaf where
  margin := (4812727/8437906)
  polygon := [baselineEdge leaf002p0 leaf002p1, baselineEdge leaf002p1 leaf002p2, baselineEdge leaf002p2 leaf002p3, baselineEdge leaf002p3 leaf002p4, baselineEdge leaf002p4 leaf002p0]
  vertices := [leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4]
  implications := [[(9, (213942323125350183080099100330248641489262891/259079729377363592307896800000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (461923141447762994022733788175444093654349/467915202265728493506300000000000000000000))], [(0, (13073942909659666418056450512133530037/18806721314275000000000000000000000000))], [(2, (504057919782512638819136205300595471837/905255682466400000000000000000000000000))]]

theorem leaf002_checked : leaf002.Check 0 [point] (157/2048) (109/1024) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf002, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf002, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf002]
      · intro v hv
        simp only [leaf002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf002p4, by simp [leaf002], leaf002p1, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p4, leaf002p0, leaf002p1]
        · refine ⟨leaf002p0, by simp [leaf002], leaf002p2, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p0, leaf002p1, leaf002p2]
        · refine ⟨leaf002p1, by simp [leaf002], leaf002p3, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p1, leaf002p2, leaf002p3]
        · refine ⟨leaf002p2, by simp [leaf002], leaf002p4, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p2, leaf002p3, leaf002p4]
        · refine ⟨leaf002p3, by simp [leaf002], leaf002p0, by simp [leaf002],
            by simp [leaf002], by simp [leaf002], ?_⟩
          norm_num [leaf002p3, leaf002p4, leaf002p0]
    · intro v hv
      simp only [leaf002, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf002, point, leaf002p0, leaf002p1, leaf002p2, leaf002p3, leaf002p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
