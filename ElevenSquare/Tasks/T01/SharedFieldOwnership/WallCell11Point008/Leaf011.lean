import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf011p0 : QPoint := ((274805230228946049324543/85300000000000000000000), (9927811724062056767261268557124863/3802396775000000000000000000000000))
def leaf011p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf011p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf011p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf011p4 : QPoint := ((274805230228946049324543/85300000000000000000000), (66386207372872893204749198305058631/36043685600000000000000000000000000))

def leaf011 : WallOwnershipLeaf where
  margin := (5591/8530)
  polygon := [baselineEdge leaf011p0 leaf011p1, baselineEdge leaf011p1 leaf011p2, baselineEdge leaf011p2 leaf011p3, baselineEdge leaf011p3 leaf011p4, baselineEdge leaf011p4 leaf011p0]
  vertices := [leaf011p0, leaf011p1, leaf011p2, leaf011p3, leaf011p4]
  implications := [[(23, (78345695273752061760676623160687927049/94604435634306996300000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (2727999839067288286318324968369104336057/3267660109725659512800000000000000000000))], [(1, (4942941320468633875819918903220811123787/6426841448279200000000000000000000000000))]]

theorem leaf011_checked : leaf011.Check 11 [point] (13/64) (27/128) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf011, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf011, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf011p0, leaf011p1, leaf011p2, leaf011p3, leaf011p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf011]
      · intro v hv
        simp only [leaf011, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf011p4, by simp [leaf011], leaf011p1, by simp [leaf011],
            by simp [leaf011], by simp [leaf011], ?_⟩
          norm_num [leaf011p4, leaf011p0, leaf011p1]
        · refine ⟨leaf011p0, by simp [leaf011], leaf011p2, by simp [leaf011],
            by simp [leaf011], by simp [leaf011], ?_⟩
          norm_num [leaf011p0, leaf011p1, leaf011p2]
        · refine ⟨leaf011p1, by simp [leaf011], leaf011p3, by simp [leaf011],
            by simp [leaf011], by simp [leaf011], ?_⟩
          norm_num [leaf011p1, leaf011p2, leaf011p3]
        · refine ⟨leaf011p2, by simp [leaf011], leaf011p4, by simp [leaf011],
            by simp [leaf011], by simp [leaf011], ?_⟩
          norm_num [leaf011p2, leaf011p3, leaf011p4]
        · refine ⟨leaf011p3, by simp [leaf011], leaf011p0, by simp [leaf011],
            by simp [leaf011], by simp [leaf011], ?_⟩
          norm_num [leaf011p3, leaf011p4, leaf011p0]
    · intro v hv
      simp only [leaf011, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf011, point, leaf011p0, leaf011p1, leaf011p2, leaf011p3, leaf011p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
