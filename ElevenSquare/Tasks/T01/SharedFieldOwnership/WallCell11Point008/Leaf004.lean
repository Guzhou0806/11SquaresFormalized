import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf004p0 : QPoint := ((1361107815552529481862387/417700000000000000000000), (48619741050840810219050784013025267/18619708475000000000000000000000000))
def leaf004p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf004p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf004p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf004p4 : QPoint := ((1361107815552529481862387/417700000000000000000000), (324933358690600322293361549027233179/176499970400000000000000000000000000))

def leaf004 : WallOwnershipLeaf where
  margin := (5167/8354)
  polygon := [baselineEdge leaf004p0 leaf004p1, baselineEdge leaf004p1 leaf004p2, baselineEdge leaf004p2 leaf004p3, baselineEdge leaf004p3 leaf004p4, baselineEdge leaf004p4 leaf004p0]
  vertices := [leaf004p0, leaf004p1, leaf004p2, leaf004p3, leaf004p4]
  implications := [[(23, (415641929506412522830417649404681677941/463262283287808116700000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (14477797715788909472393485806421745383013/16001191416558124015200000000000000000000))], [(1, (24239582894014672491558969822688544037583/31471180222112800000000000000000000000000))]]

theorem leaf004_checked : leaf004.Check 11 [point] (9/64) (5/32) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf004, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf004, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf004p0, leaf004p1, leaf004p2, leaf004p3, leaf004p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf004]
      · intro v hv
        simp only [leaf004, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf004p4, by simp [leaf004], leaf004p1, by simp [leaf004],
            by simp [leaf004], by simp [leaf004], ?_⟩
          norm_num [leaf004p4, leaf004p0, leaf004p1]
        · refine ⟨leaf004p0, by simp [leaf004], leaf004p2, by simp [leaf004],
            by simp [leaf004], by simp [leaf004], ?_⟩
          norm_num [leaf004p0, leaf004p1, leaf004p2]
        · refine ⟨leaf004p1, by simp [leaf004], leaf004p3, by simp [leaf004],
            by simp [leaf004], by simp [leaf004], ?_⟩
          norm_num [leaf004p1, leaf004p2, leaf004p3]
        · refine ⟨leaf004p2, by simp [leaf004], leaf004p4, by simp [leaf004],
            by simp [leaf004], by simp [leaf004], ?_⟩
          norm_num [leaf004p2, leaf004p3, leaf004p4]
        · refine ⟨leaf004p3, by simp [leaf004], leaf004p0, by simp [leaf004],
            by simp [leaf004], by simp [leaf004], ?_⟩
          norm_num [leaf004p3, leaf004p4, leaf004p0]
    · intro v hv
      simp only [leaf004, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf004, point, leaf004p0, leaf004p1, leaf004p2, leaf004p3, leaf004p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
