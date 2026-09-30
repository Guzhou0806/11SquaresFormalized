import ElevenSquare.Pending.S07_GridData
namespace ElevenSquare.Pending.GridDistance

theorem lookup_left {α : Type} [Inhabited α] (as bs : Array α)
    (i : ℕ) (h : i < as.size) : (as ++ bs)[i]! = as[i]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega), getElem!_pos as i h]
  exact Array.get_append_left h

theorem lookup_right {α : Type} [Inhabited α] (as bs : Array α)
    (i : ℕ) (ha : as.size ≤ i) (hb : i-as.size < bs.size) :
    (as ++ bs)[i]! = bs[i-as.size]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega), getElem!_pos bs (i-as.size) hb]
  exact Array.get_append_right ha

theorem grid_chunk_size0 : gridChunk0.size = 16 := rfl
theorem grid_chunk_size1 : gridChunk1.size = 16 := rfl
theorem grid_chunk_size2 : gridChunk2.size = 16 := rfl
theorem grid_chunk_size3 : gridChunk3.size = 16 := rfl
theorem grid_chunk_size4 : gridChunk4.size = 16 := rfl
theorem grid_chunk_size5 : gridChunk5.size = 16 := rfl
theorem grid_chunk_size6 : gridChunk6.size = 16 := rfl
theorem grid_chunk_size7 : gridChunk7.size = 16 := rfl
theorem grid_chunk_size8 : gridChunk8.size = 16 := rfl
theorem grid_chunk_size9 : gridChunk9.size = 16 := rfl
theorem grid_chunk_size10 : gridChunk10.size = 16 := rfl
theorem grid_chunk_size11 : gridChunk11.size = 16 := rfl
theorem grid_chunk_size12 : gridChunk12.size = 16 := rfl
theorem grid_chunk_size13 : gridChunk13.size = 12 := rfl
def gridPrefix0 : Array (List GridPoint) := gridChunk0
theorem grid_prefix_size0 : gridPrefix0.size = 16 := rfl
def gridPrefix1 : Array (List GridPoint) := gridPrefix0 ++ gridChunk1
theorem grid_prefix_size1 : gridPrefix1.size = 32 := by
  rw [gridPrefix1, Array.size_append, grid_prefix_size0, grid_chunk_size1]
def gridPrefix2 : Array (List GridPoint) := gridPrefix1 ++ gridChunk2
theorem grid_prefix_size2 : gridPrefix2.size = 48 := by
  rw [gridPrefix2, Array.size_append, grid_prefix_size1, grid_chunk_size2]
def gridPrefix3 : Array (List GridPoint) := gridPrefix2 ++ gridChunk3
theorem grid_prefix_size3 : gridPrefix3.size = 64 := by
  rw [gridPrefix3, Array.size_append, grid_prefix_size2, grid_chunk_size3]
def gridPrefix4 : Array (List GridPoint) := gridPrefix3 ++ gridChunk4
theorem grid_prefix_size4 : gridPrefix4.size = 80 := by
  rw [gridPrefix4, Array.size_append, grid_prefix_size3, grid_chunk_size4]
def gridPrefix5 : Array (List GridPoint) := gridPrefix4 ++ gridChunk5
theorem grid_prefix_size5 : gridPrefix5.size = 96 := by
  rw [gridPrefix5, Array.size_append, grid_prefix_size4, grid_chunk_size5]
def gridPrefix6 : Array (List GridPoint) := gridPrefix5 ++ gridChunk6
theorem grid_prefix_size6 : gridPrefix6.size = 112 := by
  rw [gridPrefix6, Array.size_append, grid_prefix_size5, grid_chunk_size6]
def gridPrefix7 : Array (List GridPoint) := gridPrefix6 ++ gridChunk7
theorem grid_prefix_size7 : gridPrefix7.size = 128 := by
  rw [gridPrefix7, Array.size_append, grid_prefix_size6, grid_chunk_size7]
def gridPrefix8 : Array (List GridPoint) := gridPrefix7 ++ gridChunk8
theorem grid_prefix_size8 : gridPrefix8.size = 144 := by
  rw [gridPrefix8, Array.size_append, grid_prefix_size7, grid_chunk_size8]
def gridPrefix9 : Array (List GridPoint) := gridPrefix8 ++ gridChunk9
theorem grid_prefix_size9 : gridPrefix9.size = 160 := by
  rw [gridPrefix9, Array.size_append, grid_prefix_size8, grid_chunk_size9]
def gridPrefix10 : Array (List GridPoint) := gridPrefix9 ++ gridChunk10
theorem grid_prefix_size10 : gridPrefix10.size = 176 := by
  rw [gridPrefix10, Array.size_append, grid_prefix_size9, grid_chunk_size10]
def gridPrefix11 : Array (List GridPoint) := gridPrefix10 ++ gridChunk11
theorem grid_prefix_size11 : gridPrefix11.size = 192 := by
  rw [gridPrefix11, Array.size_append, grid_prefix_size10, grid_chunk_size11]
def gridPrefix12 : Array (List GridPoint) := gridPrefix11 ++ gridChunk12
theorem grid_prefix_size12 : gridPrefix12.size = 208 := by
  rw [gridPrefix12, Array.size_append, grid_prefix_size11, grid_chunk_size12]
def gridPrefix13 : Array (List GridPoint) := gridPrefix12 ++ gridChunk13
theorem grid_prefix_size13 : gridPrefix13.size = 220 := by
  rw [gridPrefix13, Array.size_append, grid_prefix_size12, grid_chunk_size13]
theorem grid_array_eq_prefix : gridArray = gridPrefix13 := rfl
theorem grid_array_size : gridArray.size = 220 := grid_prefix_size13
end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.lookup_right
