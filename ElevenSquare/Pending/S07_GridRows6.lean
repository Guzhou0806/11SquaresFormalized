import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks3
import ElevenSquare.Pending.S07_GridVertexChecks4
import ElevenSquare.Pending.S07_GridVertexChecks7
import ElevenSquare.Pending.S07_GridVertexChecks8
import ElevenSquare.Pending.S07_GridVertexChecks9
namespace ElevenSquare.Pending.GridDistance

theorem row_check96 : rowCheck rationalRow96 gridRow96 = true := by
  simp only [rowCheck, rationalRow96, gridRow96, zipCheck, vertex_check136, vertex_check137, vertex_check138, vertex_check139, Bool.true_and]

theorem row_check97 : rowCheck rationalRow97 gridRow97 = true := by
  simp only [rowCheck, rationalRow97, gridRow97, zipCheck, vertex_check138, vertex_check140, vertex_check139, Bool.true_and]

theorem row_check98 : rowCheck rationalRow98 gridRow98 = true := by
  simp only [rowCheck, rationalRow98, gridRow98, zipCheck, vertex_check131, vertex_check130, vertex_check62, vertex_check61, Bool.true_and]

theorem row_check99 : rowCheck rationalRow99 gridRow99 = true := by
  simp only [rowCheck, rationalRow99, gridRow99, zipCheck, vertex_check64, vertex_check136, vertex_check139, vertex_check133, vertex_check131, vertex_check61, Bool.true_and]

theorem row_check100 : rowCheck rationalRow100 gridRow100 = true := by
  simp only [rowCheck, rationalRow100, gridRow100, zipCheck, vertex_check139, vertex_check140, vertex_check134, vertex_check133, Bool.true_and]

theorem row_check101 : rowCheck rationalRow101 gridRow101 = true := by
  simp only [rowCheck, rationalRow101, gridRow101, zipCheck, vertex_check141, vertex_check113, vertex_check112, vertex_check135, vertex_check134, vertex_check142, Bool.true_and]

theorem row_check102 : rowCheck rationalRow102 gridRow102 = true := by
  simp only [rowCheck, rationalRow102, gridRow102, zipCheck, vertex_check137, vertex_check143, vertex_check138, Bool.true_and]

theorem row_check103 : rowCheck rationalRow103 gridRow103 = true := by
  simp only [rowCheck, rationalRow103, gridRow103, zipCheck, vertex_check143, vertex_check144, vertex_check145, vertex_check141, vertex_check142, vertex_check140, vertex_check138, Bool.true_and]

theorem row_check104 : rowCheck rationalRow104 gridRow104 = true := by
  simp only [rowCheck, rationalRow104, gridRow104, zipCheck, vertex_check144, vertex_check146, vertex_check145, Bool.true_and]

theorem row_check105 : rowCheck rationalRow105 gridRow105 = true := by
  simp only [rowCheck, rationalRow105, gridRow105, zipCheck, vertex_check134, vertex_check140, vertex_check142, Bool.true_and]

theorem row_check106 : rowCheck rationalRow106 gridRow106 = true := by
  simp only [rowCheck, rationalRow106, gridRow106, zipCheck, vertex_check51, vertex_check50, vertex_check66, vertex_check130, vertex_check129, vertex_check147, Bool.true_and]

theorem row_check107 : rowCheck rationalRow107 gridRow107 = true := by
  simp only [rowCheck, rationalRow107, gridRow107, zipCheck, vertex_check147, vertex_check129, vertex_check132, Bool.true_and]

theorem row_check108 : rowCheck rationalRow108 gridRow108 = true := by
  simp only [rowCheck, rationalRow108, gridRow108, zipCheck, vertex_check112, vertex_check56, vertex_check51, vertex_check147, vertex_check132, vertex_check135, Bool.true_and]

theorem row_check109 : rowCheck rationalRow109 gridRow109 = true := by
  simp only [rowCheck, rationalRow109, gridRow109, zipCheck, vertex_check66, vertex_check62, vertex_check130, Bool.true_and]

theorem row_check110 : rowCheck rationalRow110 gridRow110 = true := by
  simp only [rowCheck, rationalRow110, gridRow110, zipCheck, vertex_check148, vertex_check149, vertex_check150, Bool.true_and]

theorem row_check111 : rowCheck rationalRow111 gridRow111 = true := by
  simp only [rowCheck, rationalRow111, gridRow111, zipCheck, vertex_check151, vertex_check152, vertex_check153, vertex_check154, vertex_check155, vertex_check156, Bool.true_and]

theorem aligned_chunk6 : ArrayAligned Row recordedOverlayVerticesChunk6 gridChunk6 := by
  have heq : recordedOverlayVerticesChunk6 = rationalChunk6 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow96, rationalRow97, rationalRow98, rationalRow99, rationalRow100, rationalRow101, rationalRow102, rationalRow103, rationalRow104, rationalRow105, rationalRow106, rationalRow107, rationalRow108, rationalRow109, rationalRow110, rationalRow111] [gridRow96, gridRow97, gridRow98, gridRow99, gridRow100, gridRow101, gridRow102, gridRow103, gridRow104, gridRow105, gridRow106, gridRow107, gridRow108, gridRow109, gridRow110, gridRow111]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow96 gridRow96 row_check96) (List.Forall₂.cons (rowCheck_sound rationalRow97 gridRow97 row_check97) (List.Forall₂.cons (rowCheck_sound rationalRow98 gridRow98 row_check98) (List.Forall₂.cons (rowCheck_sound rationalRow99 gridRow99 row_check99) (List.Forall₂.cons (rowCheck_sound rationalRow100 gridRow100 row_check100) (List.Forall₂.cons (rowCheck_sound rationalRow101 gridRow101 row_check101) (List.Forall₂.cons (rowCheck_sound rationalRow102 gridRow102 row_check102) (List.Forall₂.cons (rowCheck_sound rationalRow103 gridRow103 row_check103) (List.Forall₂.cons (rowCheck_sound rationalRow104 gridRow104 row_check104) (List.Forall₂.cons (rowCheck_sound rationalRow105 gridRow105 row_check105) (List.Forall₂.cons (rowCheck_sound rationalRow106 gridRow106 row_check106) (List.Forall₂.cons (rowCheck_sound rationalRow107 gridRow107 row_check107) (List.Forall₂.cons (rowCheck_sound rationalRow108 gridRow108 row_check108) (List.Forall₂.cons (rowCheck_sound rationalRow109 gridRow109 row_check109) (List.Forall₂.cons (rowCheck_sound rationalRow110 gridRow110 row_check110) (List.Forall₂.cons (rowCheck_sound rationalRow111 gridRow111 row_check111) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk6
