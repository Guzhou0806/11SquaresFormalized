import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks4
import ElevenSquare.Pending.S07_GridVertexChecks5
import ElevenSquare.Pending.S07_GridVertexChecks6
import ElevenSquare.Pending.S07_GridVertexChecks7
import ElevenSquare.Pending.S07_GridVertexChecks9
import ElevenSquare.Pending.S07_GridVertexChecks10
import ElevenSquare.Pending.S07_GridVertexChecks11
namespace ElevenSquare.Pending.GridDistance

theorem row_check128 : rowCheck rationalRow128 gridRow128 = true := by
  simp only [rowCheck, rationalRow128, gridRow128, zipCheck, vertex_check173, vertex_check174, vertex_check175, vertex_check176, Bool.true_and]

theorem row_check129 : rowCheck rationalRow129 gridRow129 = true := by
  simp only [rowCheck, rationalRow129, gridRow129, zipCheck, vertex_check72, vertex_check69, vertex_check172, vertex_check177, vertex_check176, vertex_check175, Bool.true_and]

theorem row_check130 : rowCheck rationalRow130 gridRow130 = true := by
  simp only [rowCheck, rationalRow130, gridRow130, zipCheck, vertex_check177, vertex_check178, vertex_check179, vertex_check173, vertex_check176, Bool.true_and]

theorem row_check131 : rowCheck rationalRow131 gridRow131 = true := by
  simp only [rowCheck, rationalRow131, gridRow131, zipCheck, vertex_check105, vertex_check106, vertex_check180, vertex_check177, vertex_check172, Bool.true_and]

theorem row_check132 : rowCheck rationalRow132 gridRow132 = true := by
  simp only [rowCheck, rationalRow132, gridRow132, zipCheck, vertex_check118, vertex_check178, vertex_check177, vertex_check180, Bool.true_and]

theorem row_check133 : rowCheck rationalRow133 gridRow133 = true := by
  simp only [rowCheck, rationalRow133, gridRow133, zipCheck, vertex_check106, vertex_check107, vertex_check118, vertex_check180, Bool.true_and]

theorem row_check134 : rowCheck rationalRow134 gridRow134 = true := by
  simp only [rowCheck, rationalRow134, gridRow134, zipCheck, vertex_check118, vertex_check181, vertex_check179, vertex_check178, Bool.true_and]

theorem row_check135 : rowCheck rationalRow135 gridRow135 = true := by
  simp only [rowCheck, rationalRow135, gridRow135, zipCheck, vertex_check118, Bool.true_and]

theorem row_check136 : rowCheck rationalRow136 gridRow136 = true := by
  simp only [rowCheck, rationalRow136, gridRow136, zipCheck, vertex_check118, Bool.true_and]

theorem row_check137 : rowCheck rationalRow137 gridRow137 = true := by
  simp only [rowCheck, rationalRow137, gridRow137, zipCheck, vertex_check118, Bool.true_and]

theorem row_check138 : rowCheck rationalRow138 gridRow138 = true := by
  simp only [rowCheck, rationalRow138, gridRow138, zipCheck, vertex_check118, vertex_check120, vertex_check182, vertex_check181, Bool.true_and]

theorem row_check139 : rowCheck rationalRow139 gridRow139 = true := by
  simp only [rowCheck, rationalRow139, gridRow139, zipCheck, vertex_check118, Bool.true_and]

theorem row_check140 : rowCheck rationalRow140 gridRow140 = true := by
  simp only [rowCheck, rationalRow140, gridRow140, zipCheck, vertex_check152, vertex_check151, vertex_check174, vertex_check173, vertex_check183, Bool.true_and]

theorem row_check141 : rowCheck rationalRow141 gridRow141 = true := by
  simp only [rowCheck, rationalRow141, gridRow141, zipCheck, vertex_check173, vertex_check179, vertex_check184, vertex_check183, Bool.true_and]

theorem row_check142 : rowCheck rationalRow142 gridRow142 = true := by
  simp only [rowCheck, rationalRow142, gridRow142, zipCheck, vertex_check179, vertex_check181, vertex_check182, vertex_check185, vertex_check184, Bool.true_and]

theorem row_check143 : rowCheck rationalRow143 gridRow143 = true := by
  simp only [rowCheck, rationalRow143, gridRow143, zipCheck, vertex_check151, vertex_check87, vertex_check86, vertex_check175, vertex_check174, Bool.true_and]

theorem aligned_chunk8 : ArrayAligned Row recordedOverlayVerticesChunk8 gridChunk8 := by
  have heq : recordedOverlayVerticesChunk8 = rationalChunk8 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow128, rationalRow129, rationalRow130, rationalRow131, rationalRow132, rationalRow133, rationalRow134, rationalRow135, rationalRow136, rationalRow137, rationalRow138, rationalRow139, rationalRow140, rationalRow141, rationalRow142, rationalRow143] [gridRow128, gridRow129, gridRow130, gridRow131, gridRow132, gridRow133, gridRow134, gridRow135, gridRow136, gridRow137, gridRow138, gridRow139, gridRow140, gridRow141, gridRow142, gridRow143]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow128 gridRow128 row_check128) (List.Forall₂.cons (rowCheck_sound rationalRow129 gridRow129 row_check129) (List.Forall₂.cons (rowCheck_sound rationalRow130 gridRow130 row_check130) (List.Forall₂.cons (rowCheck_sound rationalRow131 gridRow131 row_check131) (List.Forall₂.cons (rowCheck_sound rationalRow132 gridRow132 row_check132) (List.Forall₂.cons (rowCheck_sound rationalRow133 gridRow133 row_check133) (List.Forall₂.cons (rowCheck_sound rationalRow134 gridRow134 row_check134) (List.Forall₂.cons (rowCheck_sound rationalRow135 gridRow135 row_check135) (List.Forall₂.cons (rowCheck_sound rationalRow136 gridRow136 row_check136) (List.Forall₂.cons (rowCheck_sound rationalRow137 gridRow137 row_check137) (List.Forall₂.cons (rowCheck_sound rationalRow138 gridRow138 row_check138) (List.Forall₂.cons (rowCheck_sound rationalRow139 gridRow139 row_check139) (List.Forall₂.cons (rowCheck_sound rationalRow140 gridRow140 row_check140) (List.Forall₂.cons (rowCheck_sound rationalRow141 gridRow141 row_check141) (List.Forall₂.cons (rowCheck_sound rationalRow142 gridRow142 row_check142) (List.Forall₂.cons (rowCheck_sound rationalRow143 gridRow143 row_check143) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk8
