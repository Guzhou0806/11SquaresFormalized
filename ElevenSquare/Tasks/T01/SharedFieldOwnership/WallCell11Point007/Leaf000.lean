import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point007.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf000p0 : QPoint := ((337708359002281417731/100000000000000000000), (77676721065501633299823210205227/42255200000000000000000000000000))
def leaf000p1 : QPoint := ((337708359002281417731/100000000000000000000), (11643624653062200196085895143171/4457675000000000000000000000000))
def leaf000p2 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf000p3 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf000p4 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))

def leaf000 : WallOwnershipLeaf where
  margin := (1/2)
  polygon := [baselineEdge leaf000p0 leaf000p1, baselineEdge leaf000p1 leaf000p2, baselineEdge leaf000p2 leaf000p3, baselineEdge leaf000p3 leaf000p4, baselineEdge leaf000p4 leaf000p0]
  vertices := [leaf000p0, leaf000p1, leaf000p2, leaf000p3, leaf000p4]
  implications := [[(1, (5829844434576555540234371516085358879/7534397946400000000000000000000000000))], [(23, (124077759535770295147334845440431333/110907896405987100000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (4325560767752863172706125402542912469/3830785591706517600000000000000000000))]]

theorem leaf000_checked : leaf000.Check 11 [point] 0 (1/16) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf000, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf000, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf000p0, leaf000p1, leaf000p2, leaf000p3, leaf000p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf000]
      · intro v hv
        simp only [leaf000, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf000p4, by simp [leaf000], leaf000p1, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p4, leaf000p0, leaf000p1]
        · refine ⟨leaf000p0, by simp [leaf000], leaf000p2, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p0, leaf000p1, leaf000p2]
        · refine ⟨leaf000p1, by simp [leaf000], leaf000p3, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p1, leaf000p2, leaf000p3]
        · refine ⟨leaf000p2, by simp [leaf000], leaf000p4, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p2, leaf000p3, leaf000p4]
        · refine ⟨leaf000p3, by simp [leaf000], leaf000p0, by simp [leaf000],
            by simp [leaf000], by simp [leaf000], ?_⟩
          norm_num [leaf000p3, leaf000p4, leaf000p0]
    · intro v hv
      simp only [leaf000, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf000, point, leaf000p0, leaf000p1, leaf000p2, leaf000p3, leaf000p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point007
