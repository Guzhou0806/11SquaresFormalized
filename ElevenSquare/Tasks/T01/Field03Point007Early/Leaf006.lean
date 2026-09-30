import ElevenSquare.Tasks.T01.Field03Point007Early.Data

namespace ElevenSquare.Tasks.T01.Field03Point007Early
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf006p0 : QPoint := ((15702560467891177602925479469244898693/14079360949600000000000000000000000000), (70063/131234))
def leaf006p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf006p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf006p3 : QPoint := ((70063/131234), (370094777546448844974952343212798493/292499260475000000000000000000000000))
def leaf006p4 : QPoint := ((70063/131234), (70063/131234))

def leaf006 : WallOwnershipLeaf where
  margin := (70063/131234)
  polygon := [baselineEdge leaf006p0 leaf006p1, baselineEdge leaf006p1 leaf006p2, baselineEdge leaf006p2 leaf006p3, baselineEdge leaf006p3 leaf006p4, baselineEdge leaf006p4 leaf006p0]
  vertices := [leaf006p0, leaf006p1, leaf006p2, leaf006p3, leaf006p4]
  implications := [[(9, (3601538622479212197816582139305634622760899/4029443940843727540095200000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (7680704431051339456682670553264782777461/7277443438471655540700000000000000000000))], [(0, (213935735783948844974952343212798493/292499260475000000000000000000000000))], [(2, (8185893550691177602925479469244898693/14079360949600000000000000000000000000))]]

theorem leaf006_checked : leaf006.Check 0 [point] (9/256) (3/64) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf006, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf006, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf006p0, leaf006p1, leaf006p2, leaf006p3, leaf006p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf006]
      · intro v hv
        simp only [leaf006, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf006p4, by simp [leaf006], leaf006p1, by simp [leaf006],
            by simp [leaf006], by simp [leaf006], ?_⟩
          norm_num [leaf006p4, leaf006p0, leaf006p1]
        · refine ⟨leaf006p0, by simp [leaf006], leaf006p2, by simp [leaf006],
            by simp [leaf006], by simp [leaf006], ?_⟩
          norm_num [leaf006p0, leaf006p1, leaf006p2]
        · refine ⟨leaf006p1, by simp [leaf006], leaf006p3, by simp [leaf006],
            by simp [leaf006], by simp [leaf006], ?_⟩
          norm_num [leaf006p1, leaf006p2, leaf006p3]
        · refine ⟨leaf006p2, by simp [leaf006], leaf006p4, by simp [leaf006],
            by simp [leaf006], by simp [leaf006], ?_⟩
          norm_num [leaf006p2, leaf006p3, leaf006p4]
        · refine ⟨leaf006p3, by simp [leaf006], leaf006p0, by simp [leaf006],
            by simp [leaf006], by simp [leaf006], ?_⟩
          norm_num [leaf006p3, leaf006p4, leaf006p0]
    · intro v hv
      simp only [leaf006, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf006, point, leaf006p0, leaf006p1, leaf006p2, leaf006p3, leaf006p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007Early
