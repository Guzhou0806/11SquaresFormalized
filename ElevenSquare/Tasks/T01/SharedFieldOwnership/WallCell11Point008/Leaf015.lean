import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf015p0 : QPoint := ((5441042103038784101427/1700000000000000000000), (197846594102057403333460217433907/75780475000000000000000000000000))
def leaf015p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf015p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf015p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf015p4 : QPoint := ((5441042103038784101427/1700000000000000000000), (1323399378113527766096994573488859/718338400000000000000000000000000))

def leaf015 : WallOwnershipLeaf where
  margin := (23/34)
  polygon := [baselineEdge leaf015p0 leaf015p1, baselineEdge leaf015p1 leaf015p2, baselineEdge leaf015p2 leaf015p3, baselineEdge leaf015p3 leaf015p4, baselineEdge leaf015p4 leaf015p0]
  vertices := [leaf015p0, leaf015p1, leaf015p2, leaf015p3, leaf015p4]
  implications := [[(23, (1487316626808095017504692372487332661/1885434238901780700000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (51776535408678673936004131843229511973/65123355059010799200000000000000000000))], [(1, (98430523210761444183984315773451100943/128084765088800000000000000000000000000))]]

theorem leaf015_checked : leaf015.Check 11 [point] (1/4) (1/2) := by
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
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
