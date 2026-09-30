import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf006p0 : QPoint := ((3544954699854024112139579994781961217/3041083602400000000000000000000000000), (97583/141730))
def leaf006p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf006p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf006p3 : QPoint := ((97583/141730), (80008358043761517287135948921087417/63178627775000000000000000000000000))
def leaf006p4 : QPoint := ((97583/141730), (97583/141730))

def leaf006 : WallOwnershipLeaf where
  margin := (97583/141730)
  polygon := [baselineEdge leaf006p0 leaf006p1, baselineEdge leaf006p1 leaf006p2, baselineEdge leaf006p2 leaf006p3, baselineEdge leaf006p3 leaf006p4, baselineEdge leaf006p4 leaf006p0]
  vertices := [leaf006p0, leaf006p1, leaf006p2, leaf006p3, leaf006p4]
  implications := [[(9, (527022633285278046481466977465881699992231/870343188100311663528800000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (1204596178812292393123176764427233282609/1571897615762055168300000000000000000000))], [(0, (36509028091261517287135948921087417/63178627775000000000000000000000000))], [(2, (1451127978814024112139579994781961217/3041083602400000000000000000000000000))]]

theorem leaf006_checked : leaf006.Check 0 [point] (73/256) (207/512) := by
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
end ElevenSquare.Tasks.T01.Field03Point007
