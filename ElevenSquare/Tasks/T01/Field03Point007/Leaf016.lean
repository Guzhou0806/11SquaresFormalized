import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf016p0 : QPoint := ((7849983474719638721776877797380919548189/7093310015240800000000000000000000000000), (33550711/66116882))
def leaf016p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf016p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf016p3 : QPoint := ((33550711/66116882), (186429434111540203013283272870019193589/147363785984675000000000000000000000000))
def leaf016p4 : QPoint := ((33550711/66116882), (33550711/66116882))

def leaf016 : WallOwnershipLeaf where
  margin := (33550711/66116882)
  polygon := [baselineEdge leaf016p0 leaf016p1, baselineEdge leaf016p1 leaf016p2, baselineEdge leaf016p2 leaf016p3, baselineEdge leaf016p3 leaf016p4, baselineEdge leaf016p4 leaf016p0]
  vertices := [leaf016p0, leaf016p1, leaf016p2, leaf016p3, leaf016p4]
  implications := [[(9, (1914522532375740787689626308333040266152040427/2030070481448250561657989600000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (4050784869393011191680755295236618236531853/3666442149771436592111100000000000000000000))], [(0, (111650351283077703013283272870019193589/147363785984675000000000000000000000000))], [(2, (4250515575511238721776877797380919548189/7093310015240800000000000000000000000000))]]

theorem leaf016_checked : leaf016.Check 0 [point] (1987/2048) (4035/4096) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf016, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf016, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf016p0, leaf016p1, leaf016p2, leaf016p3, leaf016p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf016]
      · intro v hv
        simp only [leaf016, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf016p4, by simp [leaf016], leaf016p1, by simp [leaf016],
            by simp [leaf016], by simp [leaf016], ?_⟩
          norm_num [leaf016p4, leaf016p0, leaf016p1]
        · refine ⟨leaf016p0, by simp [leaf016], leaf016p2, by simp [leaf016],
            by simp [leaf016], by simp [leaf016], ?_⟩
          norm_num [leaf016p0, leaf016p1, leaf016p2]
        · refine ⟨leaf016p1, by simp [leaf016], leaf016p3, by simp [leaf016],
            by simp [leaf016], by simp [leaf016], ?_⟩
          norm_num [leaf016p1, leaf016p2, leaf016p3]
        · refine ⟨leaf016p2, by simp [leaf016], leaf016p4, by simp [leaf016],
            by simp [leaf016], by simp [leaf016], ?_⟩
          norm_num [leaf016p2, leaf016p3, leaf016p4]
        · refine ⟨leaf016p3, by simp [leaf016], leaf016p0, by simp [leaf016],
            by simp [leaf016], by simp [leaf016], ?_⟩
          norm_num [leaf016p3, leaf016p4, leaf016p0]
    · intro v hv
      simp only [leaf016, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf016, point, leaf016p0, leaf016p1, leaf016p2, leaf016p3, leaf016p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
