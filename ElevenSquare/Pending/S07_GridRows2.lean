import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks0
import ElevenSquare.Pending.S07_GridVertexChecks1
import ElevenSquare.Pending.S07_GridVertexChecks2
import ElevenSquare.Pending.S07_GridVertexChecks3
import ElevenSquare.Pending.S07_GridVertexChecks4
import ElevenSquare.Pending.S07_GridVertexChecks5
namespace ElevenSquare.Pending.GridDistance

theorem row_check32 : rowCheck rationalRow32 gridRow32 = true := by
  simp only [rowCheck, rationalRow32, gridRow32, zipCheck, vertex_check47, vertex_check57, vertex_check58, vertex_check53, vertex_check48, Bool.true_and]

theorem row_check33 : rowCheck rationalRow33 gridRow33 = true := by
  simp only [rowCheck, rationalRow33, gridRow33, zipCheck, vertex_check39, vertex_check49, vertex_check54, vertex_check35, Bool.true_and]

theorem row_check34 : rowCheck rationalRow34 gridRow34 = true := by
  simp only [rowCheck, rationalRow34, gridRow34, zipCheck, vertex_check59, vertex_check60, vertex_check61, vertex_check62, vertex_check39, vertex_check38, Bool.true_and]

theorem row_check35 : rowCheck rationalRow35 gridRow35 = true := by
  simp only [rowCheck, rationalRow35, gridRow35, zipCheck, vertex_check60, vertex_check63, vertex_check64, vertex_check61, Bool.true_and]

theorem row_check36 : rowCheck rationalRow36 gridRow36 = true := by
  simp only [rowCheck, rationalRow36, gridRow36, zipCheck, vertex_check42, vertex_check65, vertex_check43, Bool.true_and]

theorem row_check37 : rowCheck rationalRow37 gridRow37 = true := by
  simp only [rowCheck, rationalRow37, gridRow37, zipCheck, vertex_check65, vertex_check59, vertex_check38, vertex_check43, Bool.true_and]

theorem row_check38 : rowCheck rationalRow38 gridRow38 = true := by
  simp only [rowCheck, rationalRow38, gridRow38, zipCheck, vertex_check66, vertex_check50, vertex_check49, Bool.true_and]

theorem row_check39 : rowCheck rationalRow39 gridRow39 = true := by
  simp only [rowCheck, rationalRow39, gridRow39, zipCheck, vertex_check62, vertex_check66, vertex_check49, vertex_check39, Bool.true_and]

theorem row_check40 : rowCheck rationalRow40 gridRow40 = true := by
  simp only [rowCheck, rationalRow40, gridRow40, zipCheck, vertex_check67, vertex_check68, vertex_check69, vertex_check70, vertex_check71, Bool.true_and]

theorem row_check41 : rowCheck rationalRow41 gridRow41 = true := by
  simp only [rowCheck, rationalRow41, gridRow41, zipCheck, vertex_check69, vertex_check72, vertex_check70, Bool.true_and]

theorem row_check42 : rowCheck rationalRow42 gridRow42 = true := by
  simp only [rowCheck, rationalRow42, gridRow42, zipCheck, vertex_check73, vertex_check74, vertex_check75, Bool.true_and]

theorem row_check43 : rowCheck rationalRow43 gridRow43 = true := by
  simp only [rowCheck, rationalRow43, gridRow43, zipCheck, vertex_check12, vertex_check11, vertex_check76, Bool.true_and]

theorem row_check44 : rowCheck rationalRow44 gridRow44 = true := by
  simp only [rowCheck, rationalRow44, gridRow44, zipCheck, vertex_check74, vertex_check77, vertex_check15, vertex_check12, vertex_check76, vertex_check78, vertex_check75, Bool.true_and]

theorem row_check45 : rowCheck rationalRow45 gridRow45 = true := by
  simp only [rowCheck, rationalRow45, gridRow45, zipCheck, vertex_check11, vertex_check17, vertex_check67, vertex_check71, vertex_check78, vertex_check76, Bool.true_and]

theorem row_check46 : rowCheck rationalRow46 gridRow46 = true := by
  simp only [rowCheck, rationalRow46, gridRow46, zipCheck, vertex_check77, vertex_check20, vertex_check15, Bool.true_and]

theorem row_check47 : rowCheck rationalRow47 gridRow47 = true := by
  simp only [rowCheck, rationalRow47, gridRow47, zipCheck, vertex_check79, vertex_check73, vertex_check75, vertex_check80, vertex_check81, Bool.true_and]

theorem aligned_chunk2 : ArrayAligned Row recordedOverlayVerticesChunk2 gridChunk2 := by
  have heq : recordedOverlayVerticesChunk2 = rationalChunk2 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow32, rationalRow33, rationalRow34, rationalRow35, rationalRow36, rationalRow37, rationalRow38, rationalRow39, rationalRow40, rationalRow41, rationalRow42, rationalRow43, rationalRow44, rationalRow45, rationalRow46, rationalRow47] [gridRow32, gridRow33, gridRow34, gridRow35, gridRow36, gridRow37, gridRow38, gridRow39, gridRow40, gridRow41, gridRow42, gridRow43, gridRow44, gridRow45, gridRow46, gridRow47]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow32 gridRow32 row_check32) (List.Forall₂.cons (rowCheck_sound rationalRow33 gridRow33 row_check33) (List.Forall₂.cons (rowCheck_sound rationalRow34 gridRow34 row_check34) (List.Forall₂.cons (rowCheck_sound rationalRow35 gridRow35 row_check35) (List.Forall₂.cons (rowCheck_sound rationalRow36 gridRow36 row_check36) (List.Forall₂.cons (rowCheck_sound rationalRow37 gridRow37 row_check37) (List.Forall₂.cons (rowCheck_sound rationalRow38 gridRow38 row_check38) (List.Forall₂.cons (rowCheck_sound rationalRow39 gridRow39 row_check39) (List.Forall₂.cons (rowCheck_sound rationalRow40 gridRow40 row_check40) (List.Forall₂.cons (rowCheck_sound rationalRow41 gridRow41 row_check41) (List.Forall₂.cons (rowCheck_sound rationalRow42 gridRow42 row_check42) (List.Forall₂.cons (rowCheck_sound rationalRow43 gridRow43 row_check43) (List.Forall₂.cons (rowCheck_sound rationalRow44 gridRow44 row_check44) (List.Forall₂.cons (rowCheck_sound rationalRow45 gridRow45 row_check45) (List.Forall₂.cons (rowCheck_sound rationalRow46 gridRow46 row_check46) (List.Forall₂.cons (rowCheck_sound rationalRow47 gridRow47 row_check47) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk2
