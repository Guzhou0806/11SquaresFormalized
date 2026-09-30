import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf017p0 : QPoint := ((325708359002281417731/100000000000000000000), (11639823653062200196085895143171/4457675000000000000000000000000))
def leaf017p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf017p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf017p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf017p4 : QPoint := ((325708359002281417731/100000000000000000000), (77792525865501633299823210205227/42255200000000000000000000000000))

def leaf017 : WallOwnershipLeaf where
  margin := (31/50)
  polygon := [baselineEdge leaf017p0 leaf017p1, baselineEdge leaf017p1 leaf017p2, baselineEdge leaf017p2 leaf017p3, baselineEdge leaf017p3 leaf017p4, baselineEdge leaf017p4 leaf017p0]
  vertices := [leaf017p0, leaf017p1, leaf017p2, leaf017p3, leaf017p4]
  implications := [[(23, (99197548123770295147334845440431333/110907896405987100000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (3455240862028063172706125402542912469/3830785591706517600000000000000000000))], [(1, (5802771147494955540234371516085358879/7534397946400000000000000000000000000))]]

theorem leaf017_checked : leaf017.Check 11 [point] (5/8) (3/4) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf017, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf017, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf017p0, leaf017p1, leaf017p2, leaf017p3, leaf017p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf017]
      · intro v hv
        simp only [leaf017, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf017p4, by simp [leaf017], leaf017p1, by simp [leaf017],
            by simp [leaf017], by simp [leaf017], ?_⟩
          norm_num [leaf017p4, leaf017p0, leaf017p1]
        · refine ⟨leaf017p0, by simp [leaf017], leaf017p2, by simp [leaf017],
            by simp [leaf017], by simp [leaf017], ?_⟩
          norm_num [leaf017p0, leaf017p1, leaf017p2]
        · refine ⟨leaf017p1, by simp [leaf017], leaf017p3, by simp [leaf017],
            by simp [leaf017], by simp [leaf017], ?_⟩
          norm_num [leaf017p1, leaf017p2, leaf017p3]
        · refine ⟨leaf017p2, by simp [leaf017], leaf017p4, by simp [leaf017],
            by simp [leaf017], by simp [leaf017], ?_⟩
          norm_num [leaf017p2, leaf017p3, leaf017p4]
        · refine ⟨leaf017p3, by simp [leaf017], leaf017p0, by simp [leaf017],
            by simp [leaf017], by simp [leaf017], ?_⟩
          norm_num [leaf017p3, leaf017p4, leaf017p0]
    · intro v hv
      simp only [leaf017, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf017, point, leaf017p0, leaf017p1, leaf017p2, leaf017p3, leaf017p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
