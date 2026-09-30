import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.ArrayNodup

-- Generated proposal. Lean checks literal identities and every comparison.
namespace ElevenSquare.Pending
open OrderedData

def overlayLabelKey (a : Fin 4 → Fin 16) : ℕ :=
  4096*(a 0).val + 256*(a 1).val + 16*(a 2).val + (a 3).val

theorem overlay_label_block0 : Block overlayLabelKey recordedOverlayLabelsChunk0.toList 32 (![0, 2, 7, 0]) (![2, 5, 11, 8]) := by
  change Block overlayLabelKey [
  ![0, 2, 7, 0],
  ![0, 2, 7, 4],
  ![0, 3, 3, 0],
  ![0, 3, 7, 0],
  ![0, 7, 2, 0],
  ![0, 7, 2, 1],
  ![0, 7, 2, 5],
  ![0, 7, 3, 0],
  ![0, 7, 3, 1],
  ![0, 7, 3, 5],
  ![0, 7, 7, 0],
  ![0, 7, 7, 5],
  ![1, 1, 7, 4],
  ![1, 1, 11, 4],
  ![1, 1, 11, 8],
  ![1, 2, 7, 0],
  ![1, 2, 7, 4],
  ![1, 2, 11, 4],
  ![1, 3, 7, 0],
  ![1, 3, 7, 4],
  ![2, 0, 11, 8],
  ![2, 0, 15, 8],
  ![2, 1, 11, 4],
  ![2, 1, 11, 8],
  ![2, 1, 15, 8],
  ![2, 2, 11, 4],
  ![2, 5, 6, 9],
  ![2, 5, 10, 8],
  ![2, 5, 10, 9],
  ![2, 5, 10, 13],
  ![2, 5, 11, 4],
  ![2, 5, 11, 8]] 32 (![0, 2, 7, 0]) (![2, 5, 11, 8])
  exact ⟨adjacent_sound overlayLabelKey _ (by decide), rfl, rfl, rfl⟩

theorem overlay_label_block1 : Block overlayLabelKey recordedOverlayLabelsChunk1.toList 32 (![2, 5, 11, 9]) (![5, 3, 7, 5]) := by
  change Block overlayLabelKey [
  ![2, 5, 11, 9],
  ![2, 5, 15, 8],
  ![3, 0, 15, 8],
  ![3, 0, 15, 12],
  ![3, 1, 11, 8],
  ![3, 1, 15, 8],
  ![3, 5, 10, 8],
  ![3, 5, 15, 8],
  ![4, 6, 2, 5],
  ![4, 6, 5, 5],
  ![4, 7, 1, 1],
  ![4, 7, 2, 0],
  ![4, 7, 2, 1],
  ![4, 7, 2, 5],
  ![4, 7, 3, 1],
  ![4, 11, 1, 1],
  ![4, 11, 1, 2],
  ![4, 11, 2, 1],
  ![4, 11, 2, 2],
  ![4, 11, 2, 5],
  ![4, 11, 5, 2],
  ![4, 11, 5, 5],
  ![5, 2, 2, 5],
  ![5, 2, 6, 4],
  ![5, 2, 6, 5],
  ![5, 2, 6, 9],
  ![5, 2, 7, 0],
  ![5, 2, 7, 4],
  ![5, 2, 7, 5],
  ![5, 2, 11, 4],
  ![5, 3, 7, 0],
  ![5, 3, 7, 5]] 32 (![2, 5, 11, 9]) (![5, 3, 7, 5])
  exact ⟨adjacent_sound overlayLabelKey _ (by decide), rfl, rfl, rfl⟩

theorem overlay_label_block2 : Block overlayLabelKey recordedOverlayLabelsChunk2.toList 32 (![5, 5, 6, 4]) (![7, 0, 10, 13]) := by
  change Block overlayLabelKey [
  ![5, 5, 6, 4],
  ![5, 5, 6, 9],
  ![5, 5, 11, 4],
  ![5, 5, 11, 9],
  ![5, 6, 2, 5],
  ![5, 6, 6, 5],
  ![5, 6, 6, 9],
  ![5, 7, 2, 5],
  ![5, 7, 3, 5],
  ![5, 7, 7, 0],
  ![5, 7, 7, 5],
  ![6, 4, 10, 10],
  ![6, 4, 10, 13],
  ![6, 5, 6, 9],
  ![6, 5, 10, 9],
  ![6, 5, 10, 13],
  ![6, 6, 6, 6],
  ![6, 6, 6, 9],
  ![6, 6, 9, 6],
  ![6, 6, 9, 9],
  ![6, 9, 6, 6],
  ![6, 9, 6, 9],
  ![6, 9, 9, 6],
  ![6, 9, 9, 9],
  ![6, 9, 9, 10],
  ![6, 9, 10, 9],
  ![6, 9, 10, 10],
  ![6, 9, 10, 13],
  ![6, 9, 13, 10],
  ![7, 0, 10, 8],
  ![7, 0, 10, 12],
  ![7, 0, 10, 13]] 32 (![5, 5, 6, 4]) (![7, 0, 10, 13])
  exact ⟨adjacent_sound overlayLabelKey _ (by decide), rfl, rfl, rfl⟩

theorem overlay_label_block3 : Block overlayLabelKey recordedOverlayLabelsChunk3.toList 32 (![7, 0, 14, 12]) (![9, 6, 2, 5]) := by
  change Block overlayLabelKey [
  ![7, 0, 14, 12],
  ![7, 0, 14, 13],
  ![7, 0, 15, 8],
  ![7, 0, 15, 12],
  ![7, 0, 15, 13],
  ![7, 4, 10, 13],
  ![7, 4, 14, 12],
  ![7, 4, 14, 13],
  ![7, 4, 14, 14],
  ![7, 4, 15, 13],
  ![7, 5, 10, 8],
  ![7, 5, 10, 12],
  ![7, 5, 10, 13],
  ![7, 5, 15, 8],
  ![8, 10, 0, 7],
  ![8, 10, 5, 2],
  ![8, 10, 5, 3],
  ![8, 10, 5, 7],
  ![8, 11, 0, 2],
  ![8, 11, 1, 1],
  ![8, 11, 1, 2],
  ![8, 11, 1, 3],
  ![8, 11, 5, 2],
  ![8, 15, 0, 2],
  ![8, 15, 0, 3],
  ![8, 15, 0, 7],
  ![8, 15, 1, 2],
  ![8, 15, 1, 3],
  ![8, 15, 5, 2],
  ![8, 15, 5, 3],
  ![8, 15, 5, 7],
  ![9, 6, 2, 5]] 32 (![7, 0, 14, 12]) (![9, 6, 2, 5])
  exact ⟨adjacent_sound overlayLabelKey _ (by decide), rfl, rfl, rfl⟩

theorem overlay_label_block4 : Block overlayLabelKey recordedOverlayLabelsChunk4.toList 32 (![9, 6, 5, 2]) (![10, 13, 8, 10]) := by
  change Block overlayLabelKey [
  ![9, 6, 5, 2],
  ![9, 6, 5, 5],
  ![9, 6, 5, 6],
  ![9, 6, 6, 5],
  ![9, 6, 6, 6],
  ![9, 6, 6, 9],
  ![9, 6, 9, 6],
  ![9, 6, 9, 9],
  ![9, 9, 6, 6],
  ![9, 9, 6, 9],
  ![9, 9, 9, 6],
  ![9, 9, 9, 9],
  ![9, 10, 5, 2],
  ![9, 10, 5, 6],
  ![9, 10, 9, 6],
  ![9, 11, 5, 2],
  ![9, 11, 5, 5],
  ![10, 8, 8, 10],
  ![10, 8, 8, 15],
  ![10, 8, 12, 10],
  ![10, 8, 13, 10],
  ![10, 9, 9, 6],
  ![10, 9, 9, 10],
  ![10, 9, 13, 10],
  ![10, 10, 4, 6],
  ![10, 10, 4, 11],
  ![10, 10, 9, 6],
  ![10, 10, 9, 11],
  ![10, 12, 8, 10],
  ![10, 12, 8, 15],
  ![10, 13, 4, 11],
  ![10, 13, 8, 10]] 32 (![9, 6, 5, 2]) (![10, 13, 8, 10])
  exact ⟨adjacent_sound overlayLabelKey _ (by decide), rfl, rfl, rfl⟩

theorem overlay_label_block5 : Block overlayLabelKey recordedOverlayLabelsChunk5.toList 32 (![10, 13, 8, 11]) (![13, 10, 5, 6]) := by
  change Block overlayLabelKey [
  ![10, 13, 8, 11],
  ![10, 13, 8, 15],
  ![10, 13, 9, 6],
  ![10, 13, 9, 10],
  ![10, 13, 9, 11],
  ![10, 13, 13, 10],
  ![11, 4, 10, 10],
  ![11, 4, 10, 13],
  ![11, 4, 13, 10],
  ![11, 4, 13, 13],
  ![11, 4, 13, 14],
  ![11, 4, 14, 13],
  ![11, 4, 14, 14],
  ![11, 8, 12, 14],
  ![11, 8, 13, 10],
  ![11, 8, 13, 14],
  ![11, 8, 13, 15],
  ![11, 8, 14, 14],
  ![11, 9, 10, 10],
  ![11, 9, 13, 10],
  ![12, 10, 0, 7],
  ![12, 10, 5, 7],
  ![12, 14, 0, 7],
  ![12, 14, 4, 7],
  ![12, 15, 0, 3],
  ![12, 15, 0, 7],
  ![13, 10, 0, 7],
  ![13, 10, 4, 6],
  ![13, 10, 4, 7],
  ![13, 10, 4, 11],
  ![13, 10, 5, 2],
  ![13, 10, 5, 6]] 32 (![10, 13, 8, 11]) (![13, 10, 5, 6])
  exact ⟨adjacent_sound overlayLabelKey _ (by decide), rfl, rfl, rfl⟩

theorem overlay_label_block6 : Block overlayLabelKey recordedOverlayLabelsChunk6.toList 28 (![13, 10, 5, 7]) (![15, 13, 8, 15]) := by
  change Block overlayLabelKey [
  ![13, 10, 5, 7],
  ![13, 10, 9, 6],
  ![13, 13, 4, 11],
  ![13, 14, 0, 7],
  ![13, 14, 4, 7],
  ![13, 14, 4, 11],
  ![13, 15, 0, 7],
  ![13, 15, 4, 7],
  ![14, 12, 8, 11],
  ![14, 12, 8, 15],
  ![14, 13, 4, 11],
  ![14, 13, 8, 11],
  ![14, 13, 8, 15],
  ![14, 14, 4, 7],
  ![14, 14, 4, 11],
  ![14, 14, 8, 11],
  ![15, 8, 8, 10],
  ![15, 8, 8, 15],
  ![15, 8, 12, 10],
  ![15, 8, 12, 14],
  ![15, 8, 12, 15],
  ![15, 8, 13, 10],
  ![15, 8, 13, 14],
  ![15, 8, 13, 15],
  ![15, 12, 8, 15],
  ![15, 12, 12, 15],
  ![15, 13, 8, 11],
  ![15, 13, 8, 15]] 28 (![13, 10, 5, 7]) (![15, 13, 8, 15])
  exact ⟨adjacent_sound overlayLabelKey _ (by decide), rfl, rfl, rfl⟩

theorem overlay_label_prefix1 : Block overlayLabelKey (recordedOverlayLabelsChunk0 ++ recordedOverlayLabelsChunk1).toList 64 (![0, 2, 7, 0]) (![5, 3, 7, 5]) := by
  rw [array_toList_append]
  exact overlay_label_block0.append overlay_label_block1 (by decide)

theorem overlay_label_prefix2 : Block overlayLabelKey (recordedOverlayLabelsChunk0 ++ recordedOverlayLabelsChunk1 ++ recordedOverlayLabelsChunk2).toList 96 (![0, 2, 7, 0]) (![7, 0, 10, 13]) := by
  rw [array_toList_append]
  exact overlay_label_prefix1.append overlay_label_block2 (by decide)

theorem overlay_label_prefix3 : Block overlayLabelKey (recordedOverlayLabelsChunk0 ++ recordedOverlayLabelsChunk1 ++ recordedOverlayLabelsChunk2 ++ recordedOverlayLabelsChunk3).toList 128 (![0, 2, 7, 0]) (![9, 6, 2, 5]) := by
  rw [array_toList_append]
  exact overlay_label_prefix2.append overlay_label_block3 (by decide)

theorem overlay_label_prefix4 : Block overlayLabelKey (recordedOverlayLabelsChunk0 ++ recordedOverlayLabelsChunk1 ++ recordedOverlayLabelsChunk2 ++ recordedOverlayLabelsChunk3 ++ recordedOverlayLabelsChunk4).toList 160 (![0, 2, 7, 0]) (![10, 13, 8, 10]) := by
  rw [array_toList_append]
  exact overlay_label_prefix3.append overlay_label_block4 (by decide)

theorem overlay_label_prefix5 : Block overlayLabelKey (recordedOverlayLabelsChunk0 ++ recordedOverlayLabelsChunk1 ++ recordedOverlayLabelsChunk2 ++ recordedOverlayLabelsChunk3 ++ recordedOverlayLabelsChunk4 ++ recordedOverlayLabelsChunk5).toList 192 (![0, 2, 7, 0]) (![13, 10, 5, 6]) := by
  rw [array_toList_append]
  exact overlay_label_prefix4.append overlay_label_block5 (by decide)

theorem overlay_label_prefix6 : Block overlayLabelKey (recordedOverlayLabelsChunk0 ++ recordedOverlayLabelsChunk1 ++ recordedOverlayLabelsChunk2 ++ recordedOverlayLabelsChunk3 ++ recordedOverlayLabelsChunk4 ++ recordedOverlayLabelsChunk5 ++ recordedOverlayLabelsChunk6).toList 220 (![0, 2, 7, 0]) (![15, 13, 8, 15]) := by
  rw [array_toList_append]
  exact overlay_label_prefix5.append overlay_label_block6 (by decide)

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.overlay_label_prefix6
