import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf013p0 : QPoint := ((344861069209447961225363/107300000000000000000000), (12488066127735740810400165488622483/4783085275000000000000000000000000))
def leaf013p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf013p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf013p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf013p4 : QPoint := ((344861069209447961225363/107300000000000000000000), (83516003703283252530710304550208571/45339829600000000000000000000000000))

def leaf013 : WallOwnershipLeaf where
  margin := (1423/2146)
  polygon := [baselineEdge leaf013p0 leaf013p1, baselineEdge leaf013p1 leaf013p2, baselineEdge leaf013p2 leaf013p3, baselineEdge leaf013p3 leaf013p4, baselineEdge leaf013p4 leaf013p0]
  vertices := [leaf013p0, leaf013p1, leaf013p2, leaf013p3, leaf013p4]
  implications := [[(23, (96851794339381526693090289157582820309/119004172843624158300000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (3372110174616822184313672556928545079237/4110432939901093384800000000000000000000))], [(1, (6215941201306644094671480636759590077167/8084408996487200000000000000000000000000))]]

theorem leaf013_checked : leaf013.Check 11 [point] (7/32) (15/64) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf013, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf013, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf013p0, leaf013p1, leaf013p2, leaf013p3, leaf013p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf013]
      · intro v hv
        simp only [leaf013, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf013p4, by simp [leaf013], leaf013p1, by simp [leaf013],
            by simp [leaf013], by simp [leaf013], ?_⟩
          norm_num [leaf013p4, leaf013p0, leaf013p1]
        · refine ⟨leaf013p0, by simp [leaf013], leaf013p2, by simp [leaf013],
            by simp [leaf013], by simp [leaf013], ?_⟩
          norm_num [leaf013p0, leaf013p1, leaf013p2]
        · refine ⟨leaf013p1, by simp [leaf013], leaf013p3, by simp [leaf013],
            by simp [leaf013], by simp [leaf013], ?_⟩
          norm_num [leaf013p1, leaf013p2, leaf013p3]
        · refine ⟨leaf013p2, by simp [leaf013], leaf013p4, by simp [leaf013],
            by simp [leaf013], by simp [leaf013], ?_⟩
          norm_num [leaf013p2, leaf013p3, leaf013p4]
        · refine ⟨leaf013p3, by simp [leaf013], leaf013p0, by simp [leaf013],
            by simp [leaf013], by simp [leaf013], ?_⟩
          norm_num [leaf013p3, leaf013p4, leaf013p0]
    · intro v hv
      simp only [leaf013, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf013, point, leaf013p0, leaf013p1, leaf013p2, leaf013p3, leaf013p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point008
