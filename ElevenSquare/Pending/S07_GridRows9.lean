import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_GridVertexChecks4
import ElevenSquare.Pending.S07_GridVertexChecks5
import ElevenSquare.Pending.S07_GridVertexChecks7
import ElevenSquare.Pending.S07_GridVertexChecks8
import ElevenSquare.Pending.S07_GridVertexChecks10
import ElevenSquare.Pending.S07_GridVertexChecks11
import ElevenSquare.Pending.S07_GridVertexChecks12
import ElevenSquare.Pending.S07_GridVertexChecks13
namespace ElevenSquare.Pending.GridDistance

theorem row_check144 : rowCheck rationalRow144 gridRow144 = true := by
  simp only [rowCheck, rationalRow144, gridRow144, zipCheck, vertex_check86, vertex_check72, vertex_check175, Bool.true_and]

theorem row_check145 : rowCheck rationalRow145 gridRow145 = true := by
  simp only [rowCheck, rationalRow145, gridRow145, zipCheck, vertex_check186, vertex_check187, vertex_check188, vertex_check189, vertex_check190, vertex_check191, Bool.true_and]

theorem row_check146 : rowCheck rationalRow146 gridRow146 = true := by
  simp only [rowCheck, rationalRow146, gridRow146, zipCheck, vertex_check187, vertex_check192, vertex_check188, Bool.true_and]

theorem row_check147 : rowCheck rationalRow147 gridRow147 = true := by
  simp only [rowCheck, rationalRow147, gridRow147, zipCheck, vertex_check193, vertex_check186, vertex_check191, Bool.true_and]

theorem row_check148 : rowCheck rationalRow148 gridRow148 = true := by
  simp only [rowCheck, rationalRow148, gridRow148, zipCheck, vertex_check194, vertex_check195, vertex_check193, vertex_check191, vertex_check190, vertex_check196, Bool.true_and]

theorem row_check149 : rowCheck rationalRow149 gridRow149 = true := by
  simp only [rowCheck, rationalRow149, gridRow149, zipCheck, vertex_check182, vertex_check120, vertex_check122, vertex_check197, vertex_check198, Bool.true_and]

theorem row_check150 : rowCheck rationalRow150 gridRow150 = true := by
  simp only [rowCheck, rationalRow150, gridRow150, zipCheck, vertex_check122, vertex_check125, vertex_check199, vertex_check197, Bool.true_and]

theorem row_check151 : rowCheck rationalRow151 gridRow151 = true := by
  simp only [rowCheck, rationalRow151, gridRow151, zipCheck, vertex_check125, vertex_check128, vertex_check194, vertex_check196, vertex_check199, Bool.true_and]

theorem row_check152 : rowCheck rationalRow152 gridRow152 = true := by
  simp only [rowCheck, rationalRow152, gridRow152, zipCheck, vertex_check200, vertex_check201, vertex_check202, Bool.true_and]

theorem row_check153 : rowCheck rationalRow153 gridRow153 = true := by
  simp only [rowCheck, rationalRow153, gridRow153, zipCheck, vertex_check203, vertex_check200, vertex_check202, vertex_check204, Bool.true_and]

theorem row_check154 : rowCheck rationalRow154 gridRow154 = true := by
  simp only [rowCheck, rationalRow154, gridRow154, zipCheck, vertex_check201, vertex_check185, vertex_check182, vertex_check198, vertex_check205, vertex_check202, Bool.true_and]

theorem row_check155 : rowCheck rationalRow155 gridRow155 = true := by
  simp only [rowCheck, rationalRow155, gridRow155, zipCheck, vertex_check205, vertex_check204, vertex_check202, Bool.true_and]

theorem row_check156 : rowCheck rationalRow156 gridRow156 = true := by
  simp only [rowCheck, rationalRow156, gridRow156, zipCheck, vertex_check189, vertex_check188, vertex_check206, Bool.true_and]

theorem row_check157 : rowCheck rationalRow157 gridRow157 = true := by
  simp only [rowCheck, rationalRow157, gridRow157, zipCheck, vertex_check188, vertex_check192, vertex_check207, vertex_check206, Bool.true_and]

theorem row_check158 : rowCheck rationalRow158 gridRow158 = true := by
  simp only [rowCheck, rationalRow158, gridRow158, zipCheck, vertex_check208, vertex_check203, vertex_check204, vertex_check209, vertex_check210, Bool.true_and]

theorem row_check159 : rowCheck rationalRow159 gridRow159 = true := by
  simp only [rowCheck, rationalRow159, gridRow159, zipCheck, vertex_check190, vertex_check189, vertex_check206, vertex_check211, vertex_check212, vertex_check213, Bool.true_and]

theorem aligned_chunk9 : ArrayAligned Row recordedOverlayVerticesChunk9 gridChunk9 := by
  have heq : recordedOverlayVerticesChunk9 = rationalChunk9 := rfl
  rw [heq]
  change List.Forall₂ Row [rationalRow144, rationalRow145, rationalRow146, rationalRow147, rationalRow148, rationalRow149, rationalRow150, rationalRow151, rationalRow152, rationalRow153, rationalRow154, rationalRow155, rationalRow156, rationalRow157, rationalRow158, rationalRow159] [gridRow144, gridRow145, gridRow146, gridRow147, gridRow148, gridRow149, gridRow150, gridRow151, gridRow152, gridRow153, gridRow154, gridRow155, gridRow156, gridRow157, gridRow158, gridRow159]
  exact (List.Forall₂.cons (rowCheck_sound rationalRow144 gridRow144 row_check144) (List.Forall₂.cons (rowCheck_sound rationalRow145 gridRow145 row_check145) (List.Forall₂.cons (rowCheck_sound rationalRow146 gridRow146 row_check146) (List.Forall₂.cons (rowCheck_sound rationalRow147 gridRow147 row_check147) (List.Forall₂.cons (rowCheck_sound rationalRow148 gridRow148 row_check148) (List.Forall₂.cons (rowCheck_sound rationalRow149 gridRow149 row_check149) (List.Forall₂.cons (rowCheck_sound rationalRow150 gridRow150 row_check150) (List.Forall₂.cons (rowCheck_sound rationalRow151 gridRow151 row_check151) (List.Forall₂.cons (rowCheck_sound rationalRow152 gridRow152 row_check152) (List.Forall₂.cons (rowCheck_sound rationalRow153 gridRow153 row_check153) (List.Forall₂.cons (rowCheck_sound rationalRow154 gridRow154 row_check154) (List.Forall₂.cons (rowCheck_sound rationalRow155 gridRow155 row_check155) (List.Forall₂.cons (rowCheck_sound rationalRow156 gridRow156 row_check156) (List.Forall₂.cons (rowCheck_sound rationalRow157 gridRow157 row_check157) (List.Forall₂.cons (rowCheck_sound rationalRow158 gridRow158 row_check158) (List.Forall₂.cons (rowCheck_sound rationalRow159 gridRow159 row_check159) List.Forall₂.nil))))))))))))))))

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.aligned_chunk9
