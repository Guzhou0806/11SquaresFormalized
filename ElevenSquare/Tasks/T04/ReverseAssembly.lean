import ElevenSquare.Tasks.T04.ReverseAligned
namespace ElevenSquare.Pending.T04Reverse
open GridDistance OverlayVertexChecks

-- Keep the large arrays behind named lemmas during index elaboration.
set_option maxRecDepth 2048 in
theorem recorded_reverse_row (r : Fin 220) :
    ReverseRowFits (overlayVertices r) (overlayLabels r) :=
  @ArrayAligned.get! (List QPoint) (Fin 4 → Fin 16) inferInstance inferInstance
    ReverseRowFits recordedOverlayVertices recordedOverlayLabels all_reverse_aligned
    r.val (lt_of_lt_of_eq r.isLt recorded_vertices_size.symm)

theorem recorded_overlay_in_hull (r : Fin 220) (p : Point)
    (hp : ∀ g, ClosedCell (overlayLabels r g) (view g p)) :
    p ∈ rationalHull (overlayVertices r) :=
  recorded_reverse_row r p hp
end ElevenSquare.Pending.T04Reverse
#print axioms ElevenSquare.Pending.T04Reverse.recorded_overlay_in_hull
