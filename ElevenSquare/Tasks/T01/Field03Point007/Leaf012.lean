import ElevenSquare.Tasks.T01.Field03Point007.Data

namespace ElevenSquare.Tasks.T01.Field03Point007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def leaf012p0 : QPoint := ((25369287414891065482063574672942544669/22220959496800000000000000000000000000), (127351/207122))
def leaf012p1 : QPoint := ((29113004696626577898128212677257187573/22895607010960000000000000000000000000), (116004631536056790127811118144773985747/114478035054800000000000000000000000000))
def leaf012p2 : QPoint := ((227745307085770295147334845440431333/207335095100000000000000000000000000), (37595661456400799477932093876381023/29619299300000000000000000000000000))
def leaf012p3 : QPoint := ((127351/207122), (584373195211384074774083539562318069/461641280675000000000000000000000000))
def leaf012p4 : QPoint := ((127351/207122), (127351/207122))

def leaf012 : WallOwnershipLeaf where
  margin := (127351/207122)
  polygon := [baselineEdge leaf012p0 leaf012p1, baselineEdge leaf012p1 leaf012p2, baselineEdge leaf012p2 leaf012p3, baselineEdge leaf012p3 leaf012p4, baselineEdge leaf012p4 leaf012p0]
  vertices := [leaf012p0, leaf012p1, leaf012p2, leaf012p3, leaf012p4]
  implications := [[(9, (4724109525373659842426247206190938737945067/6359529450564903421061600000000000000000000))], [(13, (114126993630459996565352087471772687162039/237353142849480917114800000000000000000000))], [(12, (10383365899069407535753143928656509276813/11485732659700430063100000000000000000000))], [(0, (300528510748884074774083539562318069/461641280675000000000000000000000000))], [(2, (11706511790491065482063574672942544669/22220959496800000000000000000000000000))]]

theorem leaf012_checked : leaf012.Check 0 [point] (329/512) (195/256) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [leaf012, BaselineWallCheck]
  · rw [cellSlab_eq]
    norm_num [leaf012, BaselinePolygonImplicationCheck, BaselineImplicationCheck,
      BaselineCombinationValid, baselineCombinationSum, baselineZeroHalfplane,
      cellSlab, baselineRationalCap, baselineEdge, List.getD, leaf012p0, leaf012p1, leaf012p2, leaf012p3, leaf012p4]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    constructor
    · constructor
      · simp [leaf012]
      · intro v hv
        simp only [leaf012, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · refine ⟨leaf012p4, by simp [leaf012], leaf012p1, by simp [leaf012],
            by simp [leaf012], by simp [leaf012], ?_⟩
          norm_num [leaf012p4, leaf012p0, leaf012p1]
        · refine ⟨leaf012p0, by simp [leaf012], leaf012p2, by simp [leaf012],
            by simp [leaf012], by simp [leaf012], ?_⟩
          norm_num [leaf012p0, leaf012p1, leaf012p2]
        · refine ⟨leaf012p1, by simp [leaf012], leaf012p3, by simp [leaf012],
            by simp [leaf012], by simp [leaf012], ?_⟩
          norm_num [leaf012p1, leaf012p2, leaf012p3]
        · refine ⟨leaf012p2, by simp [leaf012], leaf012p4, by simp [leaf012],
            by simp [leaf012], by simp [leaf012], ?_⟩
          norm_num [leaf012p2, leaf012p3, leaf012p4]
        · refine ⟨leaf012p3, by simp [leaf012], leaf012p0, by simp [leaf012],
            by simp [leaf012], by simp [leaf012], ?_⟩
          norm_num [leaf012p3, leaf012p4, leaf012p0]
    · intro v hv
      simp only [leaf012, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [leaf012, point, leaf012p0, leaf012p1, leaf012p2, leaf012p3, leaf012p4, BaselineCoreVertexCheck, BaselineQuadraticCheck]

end
end ElevenSquare.Tasks.T01.Field03Point007
