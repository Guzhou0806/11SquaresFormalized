import ElevenSquare.Pending.S07_OverlayLabelBlocks
namespace ElevenSquare.Pending
open OrderedData
-- Permit traversal of the 220-label term; CPU, memory and wall caps are unchanged.
set_option maxRecDepth 2048 in
theorem overlay_inventory_nodup : Function.Injective overlayLabels := by
  have h : Block overlayLabelKey recordedOverlayLabels.toList 220 (![0, 2, 7, 0]) (![15, 13, 8, 15]) := overlay_label_prefix6
  unfold overlayLabels
  exact @OrderedData.Block.array_get_injective (Fin 4 → Fin 16) inferInstance overlayLabelKey recordedOverlayLabels 220 (![0, 2, 7, 0]) (![15, 13, 8, 15]) h
end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.overlay_inventory_nodup
