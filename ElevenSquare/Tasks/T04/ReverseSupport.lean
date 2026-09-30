import ElevenSquare.Pending.S07_OverlayVertexSupport
namespace ElevenSquare.Pending.T04Reverse
open GridDistance
/-- The reverse inclusion, with row and label order retained for assembly. -/
def ReverseRowFits (vs : List QPoint) (labels : Fin 4 → Fin 16) : Prop :=
  ∀ p, (∀ g, ClosedCell (labels g) (view g p)) → p ∈ rationalHull vs
end ElevenSquare.Pending.T04Reverse
