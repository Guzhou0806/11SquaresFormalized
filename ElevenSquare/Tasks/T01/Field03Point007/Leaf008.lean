import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf008p0 : QPoint := ((1370438265514393801462769648934990479997/1175406384418400000000000000000000000000), (7551383/10955986))
def leaf008p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf008p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf008p3 : QPoint := ((7551383/10955986), (30924083118397499849594984705995514197/24419112446275000000000000000000000000))
def leaf008p4 : QPoint := ((7551383/10955986), (7551383/10955986))

def leaf008 : WallOwnershipLeaf where
  margin := (7551383/10955986)
  polygon := [baselineEdge leaf008p0 leaf008p1, baselineEdge leaf008p1 leaf008p2, baselineEdge leaf008p2 leaf008p3, baselineEdge leaf008p3 leaf008p4, baselineEdge leaf008p4 leaf008p0]
  vertices := [leaf008p0, leaf008p1, leaf008p2, leaf008p3, leaf008p4]
  implications := [[(9, (203238815628987949722618410519244880504165771/336395533197713299275320800000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (464753841777938426425034251978764759154669/607552680156722491890300000000000000000000))], [(0, (14093277511134999849594984705995514197/24419112446275000000000000000000000000))], [(2, (560292671189193801462769648934990479997/1175406384418400000000000000000000000000))]]

theorem leaf008_checked : leaf008.Check 0 [point] (67/128) (1133/2048) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf008, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf008, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf008p0, leaf008p1, leaf008p2, leaf008p3, leaf008p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf008]
      · intro v hv
        simp only [leaf008, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf008p4, by simp [leaf008], leaf008p1, by simp [leaf008],
            by simp [leaf008], by simp [leaf008], ?_⟩
          norm_num [leaf008p4, leaf008p0, leaf008p1]
        · refine ⟨leaf008p0, by simp [leaf008], leaf008p2, by simp [leaf008],
            by simp [leaf008], by simp [leaf008], ?_⟩
          norm_num [leaf008p0, leaf008p1, leaf008p2]
        · refine ⟨leaf008p1, by simp [leaf008], leaf008p3, by simp [leaf008],
            by simp [leaf008], by simp [leaf008], ?_⟩
          norm_num [leaf008p1, leaf008p2, leaf008p3]
        · refine ⟨leaf008p2, by simp [leaf008], leaf008p4, by simp [leaf008],
            by simp [leaf008], by simp [leaf008], ?_⟩
          norm_num [leaf008p2, leaf008p3, leaf008p4]
        · refine ⟨leaf008p3, by simp [leaf008], leaf008p0, by simp [leaf008],
            by simp [leaf008], by simp [leaf008], ?_⟩
          norm_num [leaf008p3, leaf008p4, leaf008p0]
    · intro v hv
      simp only [leaf008, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf008, point, leaf008p0, leaf008p1, leaf008p2, leaf008p3, leaf008p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
