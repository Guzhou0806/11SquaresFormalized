import ElevenSquare.Cover
import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.S07_OverlayNodup
import ElevenSquare.Tasks.T04.ReverseAssembly
import ElevenSquare.Tasks.T04.Completeness.Assembly
import ElevenSquare.Tasks.T04.Forward

/-! UNFINISHED FORMALIZATION OBLIGATIONS. See handoffs/S07_Overlay.md.
Every `sorry` in this file is an explicit outstanding proof, not verified evidence. -/

namespace ElevenSquare.Pending
noncomputable section

def Overlay (labels : Fin 4 → Fin 16) : Set Point :=
  {p | ∀ g, ClosedCell (labels g) (view g p)}

theorem overlay_vertex_representation (r : Fin 220) :
    Overlay (overlayLabels r) = rationalHull (overlayVertices r) := by
  ext p
  constructor
  · exact T04Reverse.recorded_overlay_in_hull r p
  · exact T04Forward.recorded_hull_in_overlay r p

theorem overlay_inventory_complete (labels : Fin 4 → Fin 16)
    (h : (Overlay labels).Nonempty) : ∃ r : Fin 220, overlayLabels r = labels := by
  obtain ⟨p, hp⟩ := h
  exact T04Completeness.inventory_complete labels p hp

-- Injectivity of the unchanged 220 labels is proved in S07_OverlayNodup.

-- Derives a region for arbitrary independent choices of closed-cell labels.
theorem point_has_overlay (p : Point) (labels : Fin 4 → Fin 16)
    (h : ∀ g, ClosedCell (labels g) (view g p)) :
    ∃ r : Fin 220, p ∈ rationalHull (overlayVertices r) ∧ overlayLabels r = labels := by
  obtain ⟨r, hr⟩ := overlay_inventory_complete labels ⟨p, h⟩
  refine ⟨r, ?_, hr⟩
  rw [← overlay_vertex_representation, hr]
  exact h


end
end ElevenSquare.Pending

#print axioms ElevenSquare.Pending.overlay_inventory_nodup
