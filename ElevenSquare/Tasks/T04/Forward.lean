import ElevenSquare.Pending.S07_OverlayHullInclusion

namespace ElevenSquare.Pending.T04Forward
open GridDistance OverlayVertexChecks

/-- Reuse the unchanged forward inclusion already checked in the base project. -/
theorem all_vertices_aligned :
    ArrayAligned VertexRowFits recordedOverlayVertices recordedOverlayLabels :=
  OverlayVertexChecks.all_vertices_aligned

theorem recorded_hull_in_overlay (r : Fin 220) (p : Point)
    (hp : p ∈ rationalHull (overlayVertices r)) :
    ∀ g, ClosedCell (overlayLabels r g) (view g p) :=
  OverlayVertexChecks.recorded_hull_in_overlay r p hp

end ElevenSquare.Pending.T04Forward
#print axioms ElevenSquare.Pending.T04Forward.recorded_hull_in_overlay
