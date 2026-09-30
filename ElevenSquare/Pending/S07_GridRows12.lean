import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks9
import ElevenSquare.Pending.S07_GridVertexChecks11
import ElevenSquare.Pending.S07_GridVertexChecks12
import ElevenSquare.Pending.S07_GridVertexChecks13
import ElevenSquare.Pending.S07_GridVertexChecks14
import ElevenSquare.Pending.S07_GridVertexChecks15
import ElevenSquare.Pending.S07_GridVertexChecks16
namespace ElevenSquare.Pending.GridDistance

theorem row_check192 : rowCheck rationalRow192 gridRow192 = true := by
  simp only [rowCheck, rationalRow192, gridRow192, zipCheck, vertex_check233, vertex_check158, vertex_check153, vertex_check250, vertex_check244, vertex_check243, Bool.true_and]

theorem row_check193 : rowCheck rationalRow193 gridRow193 = true := by
  simp only [rowCheck, rationalRow193, gridRow193, zipCheck, vertex_check184, vertex_check185, vertex_check201, vertex_check245, Bool.true_and]

theorem row_check194 : rowCheck rationalRow194 gridRow194 = true := by
  simp only [rowCheck, rationalRow194, gridRow194, zipCheck, vertex_check249, vertex_check203, vertex_check208, vertex_check251, Bool.true_and]

theorem row_check195 : rowCheck rationalRow195 gridRow195 = true := by
  simp only [rowCheck, rationalRow195, gridRow195, zipCheck, vertex_check238, vertex_check237, vertex_check252, Bool.true_and]

theorem row_check196 : rowCheck rationalRow196 gridRow196 = true := by
  simp only [rowCheck, rationalRow196, gridRow196, zipCheck, vertex_check253, vertex_check239, vertex_check238, vertex_check252, vertex_check247, vertex_check248, vertex_check254, Bool.true_and]

theorem row_check197 : rowCheck rationalRow197 gridRow197 = true := by
  simp only [rowCheck, rationalRow197, gridRow197, zipCheck, vertex_check248, vertex_check249, vertex_check251, vertex_check254, Bool.true_and]

theorem row_check198 : rowCheck rationalRow198 gridRow198 = true := by
  simp only [rowCheck, rationalRow198, gridRow198, zipCheck, vertex_check237, vertex_check234, vertex_check242, vertex_check252, Bool.true_and]

theorem row_check199 : rowCheck rationalRow199 gridRow199 = true := by
  simp only [rowCheck, rationalRow199, gridRow199, zipCheck, vertex_check242, vertex_check247, vertex_check252, Bool.true_and]

theorem row_check200 : rowCheck rationalRow200 gridRow200 = true := by
  simp only [rowCheck, rationalRow200, gridRow200, zipCheck, vertex_check255, vertex_check256, vertex_check257, Bool.true_and]

theorem row_check201 : rowCheck rationalRow201 gridRow201 = true := by
  simp only [rowCheck, rationalRow201, gridRow201, zipCheck, vertex_check258, vertex_check255, vertex_check257, vertex_check259, Bool.true_and]

theorem row_check202 : rowCheck rationalRow202 gridRow202 = true := by
  simp only [rowCheck, rationalRow202, gridRow202, zipCheck, vertex_check260, vertex_check251, vertex_check208, vertex_check210, Bool.true_and]

theorem row_check203 : rowCheck rationalRow203 gridRow203 = true := by
  simp only [rowCheck, rationalRow203, gridRow203, zipCheck, vertex_check256, vertex_check261, vertex_check260, vertex_check210, vertex_check215, vertex_check262, vertex_check257, Bool.true_and]

theorem row_check204 : rowCheck rationalRow204 gridRow204 = true := by
  simp only [rowCheck, rationalRow204, gridRow204, zipCheck, vertex_check262, vertex_check259, vertex_check257, Bool.true_and]

theorem row_check205 : rowCheck rationalRow205 gridRow205 = true := by
  simp only [rowCheck, rationalRow205, gridRow205, zipCheck, vertex_check263, vertex_check253, vertex_check254, Bool.true_and]

theorem row_check206 : rowCheck rationalRow206 gridRow206 = true := by
  simp only [rowCheck, rationalRow206, gridRow206, zipCheck, vertex_check264, vertex_check263, vertex_check254, vertex_check251, vertex_check260, Bool.true_and]

theorem row_check207 : rowCheck rationalRow207 gridRow207 = true := by
  simp only [rowCheck, rationalRow207, gridRow207, zipCheck, vertex_check261, vertex_check264, vertex_check260, Bool.true_and]

theorem aligned_chunk12 : ArrayAligned Row recordedOverlayVerticesChunk12 gridChunk12 := by
  have heq : recordedOverlayVerticesChunk12 = rationalChunk12 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow192, rationalRow193, rationalRow194, rationalRow195, rationalRow196, rationalRow197, rationalRow198, rationalRow199, rationalRow200, rationalRow201, rationalRow202, rationalRow203, rationalRow204, rationalRow205, rationalRow206, rationalRow207] [gridRow192, gridRow193, gridRow194, gridRow195, gridRow196, gridRow197, gridRow198, gridRow199, gridRow200, gridRow201, gridRow202, gridRow203, gridRow204, gridRow205, gridRow206, gridRow207]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow192 gridRow192 row_check192) (List.Forall₂.cons (rowCheck_sound rationalRow193 gridRow193 row_check193) (List.Forall₂.cons (rowCheck_sound rationalRow194 gridRow194 row_check194) (List.Forall₂.cons (rowCheck_sound rationalRow195 gridRow195 row_check195) (List.Forall₂.cons (rowCheck_sound rationalRow196 gridRow196 row_check196) (List.Forall₂.cons (rowCheck_sound rationalRow197 gridRow197 row_check197) (List.Forall₂.cons (rowCheck_sound rationalRow198 gridRow198 row_check198) (List.Forall₂.cons (rowCheck_sound rationalRow199 gridRow199 row_check199) (List.Forall₂.cons (rowCheck_sound rationalRow200 gridRow200 row_check200) (List.Forall₂.cons (rowCheck_sound rationalRow201 gridRow201 row_check201) (List.Forall₂.cons (rowCheck_sound rationalRow202 gridRow202 row_check202) (List.Forall₂.cons (rowCheck_sound rationalRow203 gridRow203 row_check203) (List.Forall₂.cons (rowCheck_sound rationalRow204 gridRow204 row_check204) (List.Forall₂.cons (rowCheck_sound rationalRow205 gridRow205 row_check205) (List.Forall₂.cons (rowCheck_sound rationalRow206 gridRow206 row_check206) (List.Forall₂.cons (rowCheck_sound rationalRow207 gridRow207 row_check207) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk12
