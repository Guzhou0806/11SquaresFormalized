import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks6
import ElevenSquare.Pending.S07_GridVertexChecks7
import ElevenSquare.Pending.S07_GridVertexChecks8
import ElevenSquare.Pending.S07_GridVertexChecks9
import ElevenSquare.Pending.S07_GridVertexChecks10
import ElevenSquare.Pending.S07_GridVertexChecks11
import ElevenSquare.Pending.S07_GridVertexChecks12
import ElevenSquare.Pending.S07_GridVertexChecks13
import ElevenSquare.Pending.S07_GridVertexChecks14
import ElevenSquare.Pending.S07_GridVertexChecks15
namespace ElevenSquare.Pending.GridDistance

theorem row_check176 : rowCheck rationalRow176 gridRow176 = true := by
  simp only [rowCheck, rationalRow176, gridRow176, zipCheck, vertex_check232, vertex_check230, vertex_check229, Bool.true_and]

theorem row_check177 : rowCheck rationalRow177 gridRow177 = true := by
  simp only [rowCheck, rationalRow177, gridRow177, zipCheck, vertex_check225, vertex_check231, vertex_check224, Bool.true_and]

theorem row_check178 : rowCheck rationalRow178 gridRow178 = true := by
  simp only [rowCheck, rationalRow178, gridRow178, zipCheck, vertex_check127, vertex_check110, vertex_check217, Bool.true_and]

theorem row_check179 : rowCheck rationalRow179 gridRow179 = true := by
  simp only [rowCheck, rationalRow179, gridRow179, zipCheck, vertex_check194, vertex_check128, vertex_check127, vertex_check217, vertex_check221, Bool.true_and]

theorem row_check180 : rowCheck rationalRow180 gridRow180 = true := by
  simp only [rowCheck, rationalRow180, gridRow180, zipCheck, vertex_check149, vertex_check148, vertex_check233, vertex_check234, Bool.true_and]

theorem row_check181 : rowCheck rationalRow181 gridRow181 = true := by
  simp only [rowCheck, rationalRow181, gridRow181, zipCheck, vertex_check148, vertex_check158, vertex_check233, Bool.true_and]

theorem row_check182 : rowCheck rationalRow182 gridRow182 = true := by
  simp only [rowCheck, rationalRow182, gridRow182, zipCheck, vertex_check235, vertex_check236, vertex_check237, vertex_check238, Bool.true_and]

theorem row_check183 : rowCheck rationalRow183 gridRow183 = true := by
  simp only [rowCheck, rationalRow183, gridRow183, zipCheck, vertex_check239, vertex_check235, vertex_check238, Bool.true_and]

theorem row_check184 : rowCheck rationalRow184 gridRow184 = true := by
  simp only [rowCheck, rationalRow184, gridRow184, zipCheck, vertex_check240, vertex_check241, vertex_check168, vertex_check171, Bool.true_and]

theorem row_check185 : rowCheck rationalRow185 gridRow185 = true := by
  simp only [rowCheck, rationalRow185, gridRow185, zipCheck, vertex_check236, vertex_check240, vertex_check171, vertex_check149, vertex_check234, vertex_check237, Bool.true_and]

theorem row_check186 : rowCheck rationalRow186 gridRow186 = true := by
  simp only [rowCheck, rationalRow186, gridRow186, zipCheck, vertex_check242, vertex_check234, vertex_check233, vertex_check243, Bool.true_and]

theorem row_check187 : rowCheck rationalRow187 gridRow187 = true := by
  simp only [rowCheck, rationalRow187, gridRow187, zipCheck, vertex_check244, vertex_check245, vertex_check201, vertex_check200, vertex_check246, Bool.true_and]

theorem row_check188 : rowCheck rationalRow188 gridRow188 = true := by
  simp only [rowCheck, rationalRow188, gridRow188, zipCheck, vertex_check247, vertex_check242, vertex_check243, vertex_check244, vertex_check246, vertex_check248, Bool.true_and]

theorem row_check189 : rowCheck rationalRow189 gridRow189 = true := by
  simp only [rowCheck, rationalRow189, gridRow189, zipCheck, vertex_check200, vertex_check203, vertex_check249, vertex_check248, vertex_check246, Bool.true_and]

theorem row_check190 : rowCheck rationalRow190 gridRow190 = true := by
  simp only [rowCheck, rationalRow190, gridRow190, zipCheck, vertex_check153, vertex_check152, vertex_check183, vertex_check250, Bool.true_and]

theorem row_check191 : rowCheck rationalRow191 gridRow191 = true := by
  simp only [rowCheck, rationalRow191, gridRow191, zipCheck, vertex_check183, vertex_check184, vertex_check245, vertex_check244, vertex_check250, Bool.true_and]

theorem aligned_chunk11 : ArrayAligned Row recordedOverlayVerticesChunk11 gridChunk11 := by
  have heq : recordedOverlayVerticesChunk11 = rationalChunk11 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow176, rationalRow177, rationalRow178, rationalRow179, rationalRow180, rationalRow181, rationalRow182, rationalRow183, rationalRow184, rationalRow185, rationalRow186, rationalRow187, rationalRow188, rationalRow189, rationalRow190, rationalRow191] [gridRow176, gridRow177, gridRow178, gridRow179, gridRow180, gridRow181, gridRow182, gridRow183, gridRow184, gridRow185, gridRow186, gridRow187, gridRow188, gridRow189, gridRow190, gridRow191]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow176 gridRow176 row_check176) (List.Forall₂.cons (rowCheck_sound rationalRow177 gridRow177 row_check177) (List.Forall₂.cons (rowCheck_sound rationalRow178 gridRow178 row_check178) (List.Forall₂.cons (rowCheck_sound rationalRow179 gridRow179 row_check179) (List.Forall₂.cons (rowCheck_sound rationalRow180 gridRow180 row_check180) (List.Forall₂.cons (rowCheck_sound rationalRow181 gridRow181 row_check181) (List.Forall₂.cons (rowCheck_sound rationalRow182 gridRow182 row_check182) (List.Forall₂.cons (rowCheck_sound rationalRow183 gridRow183 row_check183) (List.Forall₂.cons (rowCheck_sound rationalRow184 gridRow184 row_check184) (List.Forall₂.cons (rowCheck_sound rationalRow185 gridRow185 row_check185) (List.Forall₂.cons (rowCheck_sound rationalRow186 gridRow186 row_check186) (List.Forall₂.cons (rowCheck_sound rationalRow187 gridRow187 row_check187) (List.Forall₂.cons (rowCheck_sound rationalRow188 gridRow188 row_check188) (List.Forall₂.cons (rowCheck_sound rationalRow189 gridRow189 row_check189) (List.Forall₂.cons (rowCheck_sound rationalRow190 gridRow190 row_check190) (List.Forall₂.cons (rowCheck_sound rationalRow191 gridRow191 row_check191) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk11
