import ElevenSquare.Cover
import ElevenSquare.Pending.S07_GridAlignment
import ElevenSquare.Pending.S07_GridLookupSupport
namespace ElevenSquare.Pending.OverlayVertexChecks
open GridDistance
def VertexRowFits (vs : List QPoint) (labels : Fin 4 → Fin 16) : Prop :=
  ∀ p ∈ rationalHull vs, ∀ g, ClosedCell (labels g) (view g p)
theorem recorded_vertices_size : recordedOverlayVertices.size = 220 :=
  (List.Forall₂.length_eq full_alignment).trans grid_array_size
end ElevenSquare.Pending.OverlayVertexChecks
