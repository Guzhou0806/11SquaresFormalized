import ElevenSquare.Pending.S07_EncodedSemanticSupport
namespace ElevenSquare.Pending.EncodedSearch


theorem lookup_left {α : Type} [Inhabited α] (as bs : Array α)
    (i : ℕ) (h : i < as.size) : (as ++ bs)[i]! = as[i]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega), getElem!_pos as i h]
  exact Array.get_append_left h

theorem lookup_right {α : Type} [Inhabited α] (as bs : Array α)
    (i : ℕ) (ha : as.size ≤ i) (hb : i-as.size < bs.size) :
    (as ++ bs)[i]! = bs[i-as.size]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega), getElem!_pos bs (i-as.size) hb]
  exact Array.get_append_right ha


theorem label_chunk_size0 : recordedOverlayLabelsChunk0.size = 32 := rfl
theorem label_chunk_size1 : recordedOverlayLabelsChunk1.size = 32 := rfl
theorem label_chunk_size2 : recordedOverlayLabelsChunk2.size = 32 := rfl
theorem label_chunk_size3 : recordedOverlayLabelsChunk3.size = 32 := rfl
theorem label_chunk_size4 : recordedOverlayLabelsChunk4.size = 32 := rfl
theorem label_chunk_size5 : recordedOverlayLabelsChunk5.size = 32 := rfl
theorem label_chunk_size6 : recordedOverlayLabelsChunk6.size = 28 := rfl
def labelPrefix0 : Array (Fin 4 → Fin 16) := recordedOverlayLabelsChunk0
theorem label_prefix_size0 : labelPrefix0.size = 32 := rfl
def labelPrefix1 : Array (Fin 4 → Fin 16) := labelPrefix0 ++ recordedOverlayLabelsChunk1
theorem label_prefix_size1 : labelPrefix1.size = 64 := by
  rw [labelPrefix1, Array.size_append, label_prefix_size0, label_chunk_size1]
def labelPrefix2 : Array (Fin 4 → Fin 16) := labelPrefix1 ++ recordedOverlayLabelsChunk2
theorem label_prefix_size2 : labelPrefix2.size = 96 := by
  rw [labelPrefix2, Array.size_append, label_prefix_size1, label_chunk_size2]
def labelPrefix3 : Array (Fin 4 → Fin 16) := labelPrefix2 ++ recordedOverlayLabelsChunk3
theorem label_prefix_size3 : labelPrefix3.size = 128 := by
  rw [labelPrefix3, Array.size_append, label_prefix_size2, label_chunk_size3]
def labelPrefix4 : Array (Fin 4 → Fin 16) := labelPrefix3 ++ recordedOverlayLabelsChunk4
theorem label_prefix_size4 : labelPrefix4.size = 160 := by
  rw [labelPrefix4, Array.size_append, label_prefix_size3, label_chunk_size4]
def labelPrefix5 : Array (Fin 4 → Fin 16) := labelPrefix4 ++ recordedOverlayLabelsChunk5
theorem label_prefix_size5 : labelPrefix5.size = 192 := by
  rw [labelPrefix5, Array.size_append, label_prefix_size4, label_chunk_size5]
def labelPrefix6 : Array (Fin 4 → Fin 16) := labelPrefix5 ++ recordedOverlayLabelsChunk6
theorem label_prefix_size6 : labelPrefix6.size = 220 := by
  rw [labelPrefix6, Array.size_append, label_prefix_size5, label_chunk_size6]
theorem label_array_eq_prefix : recordedOverlayLabels = labelPrefix6 := rfl
end ElevenSquare.Pending.EncodedSearch
