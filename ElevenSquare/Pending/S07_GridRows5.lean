import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks6
import ElevenSquare.Pending.S07_GridVertexChecks7
import ElevenSquare.Pending.S07_GridVertexChecks8
namespace ElevenSquare.Pending.GridDistance

theorem row_check80 : rowCheck rationalRow80 gridRow80 = true := by
  simp only [rowCheck, rationalRow80, gridRow80, zipCheck, vertex_check118, Bool.true_and]

theorem row_check81 : rowCheck rationalRow81 gridRow81 = true := by
  simp only [rowCheck, rationalRow81, gridRow81, zipCheck, vertex_check118, vertex_check107, vertex_check104, vertex_check116, Bool.true_and]

theorem row_check82 : rowCheck rationalRow82 gridRow82 = true := by
  simp only [rowCheck, rationalRow82, gridRow82, zipCheck, vertex_check118, Bool.true_and]

theorem row_check83 : rowCheck rationalRow83 gridRow83 = true := by
  simp only [rowCheck, rationalRow83, gridRow83, zipCheck, vertex_check118, Bool.true_and]

theorem row_check84 : rowCheck rationalRow84 gridRow84 = true := by
  simp only [rowCheck, rationalRow84, gridRow84, zipCheck, vertex_check118, Bool.true_and]

theorem row_check85 : rowCheck rationalRow85 gridRow85 = true := by
  simp only [rowCheck, rationalRow85, gridRow85, zipCheck, vertex_check118, vertex_check116, vertex_check115, vertex_check119, Bool.true_and]

theorem row_check86 : rowCheck rationalRow86 gridRow86 = true := by
  simp only [rowCheck, rationalRow86, gridRow86, zipCheck, vertex_check120, vertex_check118, vertex_check121, vertex_check122, Bool.true_and]

theorem row_check87 : rowCheck rationalRow87 gridRow87 = true := by
  simp only [rowCheck, rationalRow87, gridRow87, zipCheck, vertex_check118, vertex_check119, vertex_check123, vertex_check121, Bool.true_and]

theorem row_check88 : rowCheck rationalRow88 gridRow88 = true := by
  simp only [rowCheck, rationalRow88, gridRow88, zipCheck, vertex_check123, vertex_check124, vertex_check125, vertex_check122, vertex_check121, Bool.true_and]

theorem row_check89 : rowCheck rationalRow89 gridRow89 = true := by
  simp only [rowCheck, rationalRow89, gridRow89, zipCheck, vertex_check115, vertex_check117, vertex_check126, vertex_check123, vertex_check119, Bool.true_and]

theorem row_check90 : rowCheck rationalRow90 gridRow90 = true := by
  simp only [rowCheck, rationalRow90, gridRow90, zipCheck, vertex_check111, vertex_check110, vertex_check127, vertex_check124, vertex_check123, vertex_check126, Bool.true_and]

theorem row_check91 : rowCheck rationalRow91 gridRow91 = true := by
  simp only [rowCheck, rationalRow91, gridRow91, zipCheck, vertex_check117, vertex_check114, vertex_check111, vertex_check126, Bool.true_and]

theorem row_check92 : rowCheck rationalRow92 gridRow92 = true := by
  simp only [rowCheck, rationalRow92, gridRow92, zipCheck, vertex_check127, vertex_check128, vertex_check125, vertex_check124, Bool.true_and]

theorem row_check93 : rowCheck rationalRow93 gridRow93 = true := by
  simp only [rowCheck, rationalRow93, gridRow93, zipCheck, vertex_check129, vertex_check130, vertex_check131, Bool.true_and]

theorem row_check94 : rowCheck rationalRow94 gridRow94 = true := by
  simp only [rowCheck, rationalRow94, gridRow94, zipCheck, vertex_check132, vertex_check129, vertex_check131, vertex_check133, Bool.true_and]

theorem row_check95 : rowCheck rationalRow95 gridRow95 = true := by
  simp only [rowCheck, rationalRow95, gridRow95, zipCheck, vertex_check134, vertex_check135, vertex_check132, vertex_check133, Bool.true_and]

theorem aligned_chunk5 : ArrayAligned Row recordedOverlayVerticesChunk5 gridChunk5 := by
  have heq : recordedOverlayVerticesChunk5 = rationalChunk5 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow80, rationalRow81, rationalRow82, rationalRow83, rationalRow84, rationalRow85, rationalRow86, rationalRow87, rationalRow88, rationalRow89, rationalRow90, rationalRow91, rationalRow92, rationalRow93, rationalRow94, rationalRow95] [gridRow80, gridRow81, gridRow82, gridRow83, gridRow84, gridRow85, gridRow86, gridRow87, gridRow88, gridRow89, gridRow90, gridRow91, gridRow92, gridRow93, gridRow94, gridRow95]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow80 gridRow80 row_check80) (List.Forall₂.cons (rowCheck_sound rationalRow81 gridRow81 row_check81) (List.Forall₂.cons (rowCheck_sound rationalRow82 gridRow82 row_check82) (List.Forall₂.cons (rowCheck_sound rationalRow83 gridRow83 row_check83) (List.Forall₂.cons (rowCheck_sound rationalRow84 gridRow84 row_check84) (List.Forall₂.cons (rowCheck_sound rationalRow85 gridRow85 row_check85) (List.Forall₂.cons (rowCheck_sound rationalRow86 gridRow86 row_check86) (List.Forall₂.cons (rowCheck_sound rationalRow87 gridRow87 row_check87) (List.Forall₂.cons (rowCheck_sound rationalRow88 gridRow88 row_check88) (List.Forall₂.cons (rowCheck_sound rationalRow89 gridRow89 row_check89) (List.Forall₂.cons (rowCheck_sound rationalRow90 gridRow90 row_check90) (List.Forall₂.cons (rowCheck_sound rationalRow91 gridRow91 row_check91) (List.Forall₂.cons (rowCheck_sound rationalRow92 gridRow92 row_check92) (List.Forall₂.cons (rowCheck_sound rationalRow93 gridRow93 row_check93) (List.Forall₂.cons (rowCheck_sound rationalRow94 gridRow94 row_check94) (List.Forall₂.cons (rowCheck_sound rationalRow95 gridRow95 row_check95) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk5
