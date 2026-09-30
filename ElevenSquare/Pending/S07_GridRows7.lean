import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks4
import ElevenSquare.Pending.S07_GridVertexChecks5
import ElevenSquare.Pending.S07_GridVertexChecks6
import ElevenSquare.Pending.S07_GridVertexChecks9
import ElevenSquare.Pending.S07_GridVertexChecks10
namespace ElevenSquare.Pending.GridDistance

theorem row_check112 : rowCheck rationalRow112 gridRow112 = true := by
  simp only [rowCheck, rationalRow112, gridRow112, zipCheck, vertex_check154, vertex_check157, vertex_check155, Bool.true_and]

theorem row_check113 : rowCheck rationalRow113 gridRow113 = true := by
  simp only [rowCheck, rationalRow113, gridRow113, zipCheck, vertex_check153, vertex_check158, vertex_check148, vertex_check150, vertex_check157, vertex_check154, Bool.true_and]

theorem row_check114 : rowCheck rationalRow114 gridRow114 = true := by
  simp only [rowCheck, rationalRow114, gridRow114, zipCheck, vertex_check159, vertex_check160, vertex_check161, Bool.true_and]

theorem row_check115 : rowCheck rationalRow115 gridRow115 = true := by
  simp only [rowCheck, rationalRow115, gridRow115, zipCheck, vertex_check162, vertex_check79, vertex_check81, Bool.true_and]

theorem row_check116 : rowCheck rationalRow116 gridRow116 = true := by
  simp only [rowCheck, rationalRow116, gridRow116, zipCheck, vertex_check163, vertex_check162, vertex_check81, vertex_check83, vertex_check161, vertex_check160, vertex_check164, Bool.true_and]

theorem row_check117 : rowCheck rationalRow117 gridRow117 = true := by
  simp only [rowCheck, rationalRow117, gridRow117, zipCheck, vertex_check165, vertex_check163, vertex_check164, Bool.true_and]

theorem row_check118 : rowCheck rationalRow118 gridRow118 = true := by
  simp only [rowCheck, rationalRow118, gridRow118, zipCheck, vertex_check83, vertex_check87, vertex_check151, vertex_check156, vertex_check159, vertex_check161, Bool.true_and]

theorem row_check119 : rowCheck rationalRow119 gridRow119 = true := by
  simp only [rowCheck, rationalRow119, gridRow119, zipCheck, vertex_check166, vertex_check160, vertex_check159, vertex_check167, Bool.true_and]

theorem row_check120 : rowCheck rationalRow120 gridRow120 = true := by
  simp only [rowCheck, rationalRow120, gridRow120, zipCheck, vertex_check168, vertex_check169, vertex_check166, vertex_check167, vertex_check170, vertex_check171, Bool.true_and]

theorem row_check121 : rowCheck rationalRow121 gridRow121 = true := by
  simp only [rowCheck, rationalRow121, gridRow121, zipCheck, vertex_check170, vertex_check150, vertex_check149, vertex_check171, Bool.true_and]

theorem row_check122 : rowCheck rationalRow122 gridRow122 = true := by
  simp only [rowCheck, rationalRow122, gridRow122, zipCheck, vertex_check164, vertex_check160, vertex_check166, Bool.true_and]

theorem row_check123 : rowCheck rationalRow123 gridRow123 = true := by
  simp only [rowCheck, rationalRow123, gridRow123, zipCheck, vertex_check169, vertex_check165, vertex_check164, vertex_check166, Bool.true_and]

theorem row_check124 : rowCheck rationalRow124 gridRow124 = true := by
  simp only [rowCheck, rationalRow124, gridRow124, zipCheck, vertex_check159, vertex_check156, vertex_check155, vertex_check167, Bool.true_and]

theorem row_check125 : rowCheck rationalRow125 gridRow125 = true := by
  simp only [rowCheck, rationalRow125, gridRow125, zipCheck, vertex_check155, vertex_check157, vertex_check170, vertex_check167, Bool.true_and]

theorem row_check126 : rowCheck rationalRow126 gridRow126 = true := by
  simp only [rowCheck, rationalRow126, gridRow126, zipCheck, vertex_check157, vertex_check150, vertex_check170, Bool.true_and]

theorem row_check127 : rowCheck rationalRow127 gridRow127 = true := by
  simp only [rowCheck, rationalRow127, gridRow127, zipCheck, vertex_check69, vertex_check68, vertex_check105, vertex_check172, Bool.true_and]

theorem aligned_chunk7 : ArrayAligned Row recordedOverlayVerticesChunk7 gridChunk7 := by
  have heq : recordedOverlayVerticesChunk7 = rationalChunk7 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow112, rationalRow113, rationalRow114, rationalRow115, rationalRow116, rationalRow117, rationalRow118, rationalRow119, rationalRow120, rationalRow121, rationalRow122, rationalRow123, rationalRow124, rationalRow125, rationalRow126, rationalRow127] [gridRow112, gridRow113, gridRow114, gridRow115, gridRow116, gridRow117, gridRow118, gridRow119, gridRow120, gridRow121, gridRow122, gridRow123, gridRow124, gridRow125, gridRow126, gridRow127]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow112 gridRow112 row_check112) (List.Forall₂.cons (rowCheck_sound rationalRow113 gridRow113 row_check113) (List.Forall₂.cons (rowCheck_sound rationalRow114 gridRow114 row_check114) (List.Forall₂.cons (rowCheck_sound rationalRow115 gridRow115 row_check115) (List.Forall₂.cons (rowCheck_sound rationalRow116 gridRow116 row_check116) (List.Forall₂.cons (rowCheck_sound rationalRow117 gridRow117 row_check117) (List.Forall₂.cons (rowCheck_sound rationalRow118 gridRow118 row_check118) (List.Forall₂.cons (rowCheck_sound rationalRow119 gridRow119 row_check119) (List.Forall₂.cons (rowCheck_sound rationalRow120 gridRow120 row_check120) (List.Forall₂.cons (rowCheck_sound rationalRow121 gridRow121 row_check121) (List.Forall₂.cons (rowCheck_sound rationalRow122 gridRow122 row_check122) (List.Forall₂.cons (rowCheck_sound rationalRow123 gridRow123 row_check123) (List.Forall₂.cons (rowCheck_sound rationalRow124 gridRow124 row_check124) (List.Forall₂.cons (rowCheck_sound rationalRow125 gridRow125 row_check125) (List.Forall₂.cons (rowCheck_sound rationalRow126 gridRow126 row_check126) (List.Forall₂.cons (rowCheck_sound rationalRow127 gridRow127 row_check127) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk7
