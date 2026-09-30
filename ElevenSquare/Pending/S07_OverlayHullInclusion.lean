import ElevenSquare.Pending.S07_OverlayVertexAlignment0
import ElevenSquare.Pending.S07_OverlayVertexAlignment1
import ElevenSquare.Pending.S07_OverlayVertexAlignment2
import ElevenSquare.Pending.S07_OverlayVertexAlignment3
import ElevenSquare.Pending.S07_OverlayVertexAlignment4
import ElevenSquare.Pending.S07_OverlayVertexAlignment5
import ElevenSquare.Pending.S07_OverlayVertexAlignment6
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance

theorem all_vertices_aligned :
    ArrayAligned VertexRowFits recordedOverlayVertices recordedOverlayLabels := by
  unfold recordedOverlayVertices recordedOverlayLabels
  simpa only [Array.append_assoc] using
    ((((((vertices_aligned0.append vertices_aligned1).append vertices_aligned2).append
      vertices_aligned3).append vertices_aligned4).append vertices_aligned5).append vertices_aligned6)

set_option maxRecDepth 2048 in
theorem recorded_hull_in_overlay (r : Fin 220) (p : Point)
    (hp : p ∈ rationalHull (overlayVertices r)) :
    ∀ g, ClosedCell (overlayLabels r g) (view g p) := by
  have hr : VertexRowFits (overlayVertices r) (overlayLabels r) :=
    @ArrayAligned.get! (List QPoint) (Fin 4 → Fin 16) inferInstance inferInstance
      VertexRowFits recordedOverlayVertices recordedOverlayLabels all_vertices_aligned
      r.val (by rw [recorded_vertices_size]; exact r.isLt)
  exact hr p hp

end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.recorded_hull_in_overlay
