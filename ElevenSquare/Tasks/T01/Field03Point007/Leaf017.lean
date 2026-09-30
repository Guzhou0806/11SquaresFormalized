import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf017p0 : QPoint := ((1263996967035841817026915768162964246949/1143411601512800000000000000000000000000), (134214007/266444050))
def leaf017p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf017p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf017p3 : QPoint := ((134214007/266444050), (30051008702703502011048493799658028349/23754419611675000000000000000000000000))
def leaf017p4 : QPoint := ((134214007/266444050), (134214007/266444050))

def leaf017 : WallOwnershipLeaf where
  margin := (134214007/266444050)
  polygon := [baselineEdge leaf017p0 leaf017p1, baselineEdge leaf017p1 leaf017p2, baselineEdge leaf017p2 leaf017p3, baselineEdge leaf017p3 leaf017p4, baselineEdge leaf017p4 leaf017p0]
  vertices := [leaf017p0, leaf017p1, leaf017p2, leaf017p3, leaf017p4]
  implications := [[(9, (310883760940670392161080239070441341941459107/327238783500118317777253600000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (657082161666585382175024858505451162228373/591014981907832943435100000000000000000000))], [(0, (18085360229629002011048493799658028349/23754419611675000000000000000000000000))], [(2, (688034198532209817026915768162964246949/1143411601512800000000000000000000000000))]]

theorem leaf017_checked : leaf017.Check 0 [point] (4035/4096) (8131/8192) := by
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
end ElevenSquare.Tasks.T01.Field03Point007
