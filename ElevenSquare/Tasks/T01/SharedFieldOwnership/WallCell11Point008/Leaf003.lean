import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf003p0 : QPoint := ((4250208667029658430503/1300000000000000000000), (151322775489808602549116636861223/57949775000000000000000000000000))
def leaf003p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf003p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf003p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf003p4 : QPoint := ((4250208667029658430503/1300000000000000000000), (1011148429851521232897701732667951/549317600000000000000000000000000))

def leaf003 : WallOwnershipLeaf where
  margin := (79/130)
  polygon := [baselineEdge leaf003p0 leaf003p1, baselineEdge leaf003p1 leaf003p2, baselineEdge leaf003p2 leaf003p3, baselineEdge leaf003p3 leaf003p4, baselineEdge leaf003p4 leaf003p0]
  vertices := [leaf003p0, leaf003p1, leaf003p2, leaf003p3, leaf003p4]
  implications := [[(23, (1322741740825013836915352990725607329/1441802653277832300000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (46078557747331221245179630233057862097/49800212692184728800000000000000000000))], [(1, (75472122633543222023046829709109665427/97947173303200000000000000000000000000))]]

theorem leaf003_checked : leaf003.Check 11 [point] (1/8) (9/64) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf003, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf003, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf003p0, leaf003p1, leaf003p2, leaf003p3, leaf003p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf003]
      · intro v hv
        simp only [leaf003, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf003p4, by simp [leaf003], leaf003p1, by simp [leaf003],
            by simp [leaf003], by simp [leaf003], ?_⟩
          norm_num [leaf003p4, leaf003p0, leaf003p1]
        · refine ⟨leaf003p0, by simp [leaf003], leaf003p2, by simp [leaf003],
            by simp [leaf003], by simp [leaf003], ?_⟩
          norm_num [leaf003p0, leaf003p1, leaf003p2]
        · refine ⟨leaf003p1, by simp [leaf003], leaf003p3, by simp [leaf003],
            by simp [leaf003], by simp [leaf003], ?_⟩
          norm_num [leaf003p1, leaf003p2, leaf003p3]
        · refine ⟨leaf003p2, by simp [leaf003], leaf003p4, by simp [leaf003],
            by simp [leaf003], by simp [leaf003], ?_⟩
          norm_num [leaf003p2, leaf003p3, leaf003p4]
        · refine ⟨leaf003p3, by simp [leaf003], leaf003p0, by simp [leaf003],
            by simp [leaf003], by simp [leaf003], ?_⟩
          norm_num [leaf003p3, leaf003p4, leaf003p0]
    · intro v hv
      simp only [leaf003, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf003, point, leaf003p0, leaf003p1, leaf003p2, leaf003p3, leaf003p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
