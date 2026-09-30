import ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point007.Data

namespace ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf001p0 : QPoint := ((85291048263586324356867/25700000000000000000000), (2991936410836985450394075051794947/1145622475000000000000000000000000))
def leaf001p1 : QPoint := ((576110187762259293474862266740568667/207335095100000000000000000000000000), (77240837807603427468096065006618977/29619299300000000000000000000000000))
def leaf001p2 : QPoint := ((28717304821725314093181638244181213/10998748500000000000000000000000000), (1535249613734597078066177120722829/733249900000000000000000000000000))
def leaf001p3 : QPoint := ((20167298163025676566274108524659487531/7252665881040000000000000000000000000), (22385317617166524431794178569651538407/12087776468400000000000000000000000000))
def leaf001p4 : QPoint := ((85291048263586324356867/25700000000000000000000), (19977392913833919758054565022743339/10859586400000000000000000000000000))

def leaf001 : WallOwnershipLeaf where
  margin := (287/514)
  polygon := [baselineEdge leaf001p0 leaf001p1, baselineEdge leaf001p1 leaf001p2, baselineEdge leaf001p2 leaf001p3, baselineEdge leaf001p3 leaf001p4, baselineEdge leaf001p4 leaf001p0]
  vertices := [leaf001p0, leaf001p1, leaf001p2, leaf001p3, leaf001p4]
  implications := [[(23, (28777957774192965852865055278190852581/28503329376338684700000000000000000000))], [(18, (502874720221937423895996734729511699533/524498110232550940500000000000000000000))], [(14, (1843427852580324774480260831576872313267/3988512399004493922000000000000000000000))], [(15, (1002879129096885835385474228453528504533/984511897068575023200000000000000000000))], [(1, (1494885858800974773840233479633937231903/1936340272224800000000000000000000000000))]]

theorem leaf001_checked : leaf001.Check 11 [point] (1/16) (3/32) := by
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
end ElevenSquare.Tasks.T01.SharedFieldOwnership.WallCell11Point007
