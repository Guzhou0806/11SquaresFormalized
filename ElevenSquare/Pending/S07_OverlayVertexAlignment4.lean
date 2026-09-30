import ElevenSquare.Pending.S07_OverlayVertexSupport
import ElevenSquare.Pending.S07_OverlayVertexChecks16
import ElevenSquare.Pending.S07_OverlayVertexChecks17
import ElevenSquare.Pending.S07_OverlayVertexChecks18
import ElevenSquare.Pending.S07_OverlayVertexChecks19
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
theorem vertices_aligned4 : ArrayAligned VertexRowFits
    (recordedOverlayVerticesChunk8 ++ recordedOverlayVerticesChunk9) recordedOverlayLabelsChunk4 := by
  have hv : recordedOverlayVerticesChunk8 ++ recordedOverlayVerticesChunk9 = rationalChunk8 ++ rationalChunk9 := rfl
  rw [hv]
  change List.Forall₂ VertexRowFits [rationalRow128, rationalRow129, rationalRow130, rationalRow131, rationalRow132, rationalRow133, rationalRow134, rationalRow135, rationalRow136, rationalRow137, rationalRow138, rationalRow139, rationalRow140, rationalRow141, rationalRow142, rationalRow143, rationalRow144, rationalRow145, rationalRow146, rationalRow147, rationalRow148, rationalRow149, rationalRow150, rationalRow151, rationalRow152, rationalRow153, rationalRow154, rationalRow155, rationalRow156, rationalRow157, rationalRow158, rationalRow159] [![9,6,5,2], ![9,6,5,5], ![9,6,5,6], ![9,6,6,5], ![9,6,6,6], ![9,6,6,9], ![9,6,9,6], ![9,6,9,9], ![9,9,6,6], ![9,9,6,9], ![9,9,9,6], ![9,9,9,9], ![9,10,5,2], ![9,10,5,6], ![9,10,9,6], ![9,11,5,2], ![9,11,5,5], ![10,8,8,10], ![10,8,8,15], ![10,8,12,10], ![10,8,13,10], ![10,9,9,6], ![10,9,9,10], ![10,9,13,10], ![10,10,4,6], ![10,10,4,11], ![10,10,9,6], ![10,10,9,11], ![10,12,8,10], ![10,12,8,15], ![10,13,4,11], ![10,13,8,10]]
  exact (List.Forall₂.cons vertices_fit128 (List.Forall₂.cons vertices_fit129 (List.Forall₂.cons vertices_fit130 (List.Forall₂.cons vertices_fit131 (List.Forall₂.cons vertices_fit132 (List.Forall₂.cons vertices_fit133 (List.Forall₂.cons vertices_fit134 (List.Forall₂.cons vertices_fit135 (List.Forall₂.cons vertices_fit136 (List.Forall₂.cons vertices_fit137 (List.Forall₂.cons vertices_fit138 (List.Forall₂.cons vertices_fit139 (List.Forall₂.cons vertices_fit140 (List.Forall₂.cons vertices_fit141 (List.Forall₂.cons vertices_fit142 (List.Forall₂.cons vertices_fit143 (List.Forall₂.cons vertices_fit144 (List.Forall₂.cons vertices_fit145 (List.Forall₂.cons vertices_fit146 (List.Forall₂.cons vertices_fit147 (List.Forall₂.cons vertices_fit148 (List.Forall₂.cons vertices_fit149 (List.Forall₂.cons vertices_fit150 (List.Forall₂.cons vertices_fit151 (List.Forall₂.cons vertices_fit152 (List.Forall₂.cons vertices_fit153 (List.Forall₂.cons vertices_fit154 (List.Forall₂.cons vertices_fit155 (List.Forall₂.cons vertices_fit156 (List.Forall₂.cons vertices_fit157 (List.Forall₂.cons vertices_fit158 (List.Forall₂.cons vertices_fit159 List.Forall₂.nil))))))))))))))))))))))))))))))))
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.vertices_aligned4
