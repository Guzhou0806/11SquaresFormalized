import ElevenSquare.Pending.S07_GridLookupSupport
namespace ElevenSquare.Pending.GridDistance

theorem grid_lookup32 : gridArray[32]! = gridRow32 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 32 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 32 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 32 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 32 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 32 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 32 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 32 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 32 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 32 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 32 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 32 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 32
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup33 : gridArray[33]! = gridRow33 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 33 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 33 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 33 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 33 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 33 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 33 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 33 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 33 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 33 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 33 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 33 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 33
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup34 : gridArray[34]! = gridRow34 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 34 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 34 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 34 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 34 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 34 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 34 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 34 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 34 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 34 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 34 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 34 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 34
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup35 : gridArray[35]! = gridRow35 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 35 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 35 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 35 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 35 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 35 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 35 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 35 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 35 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 35 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 35 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 35 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 35
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup36 : gridArray[36]! = gridRow36 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 36 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 36 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 36 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 36 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 36 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 36 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 36 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 36 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 36 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 36 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 36 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 36
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup37 : gridArray[37]! = gridRow37 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 37 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 37 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 37 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 37 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 37 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 37 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 37 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 37 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 37 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 37 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 37 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 37
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup38 : gridArray[38]! = gridRow38 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 38 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 38 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 38 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 38 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 38 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 38 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 38 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 38 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 38 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 38 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 38 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 38
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup39 : gridArray[39]! = gridRow39 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 39 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 39 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 39 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 39 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 39 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 39 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 39 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 39 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 39 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 39 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 39 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 39
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup40 : gridArray[40]! = gridRow40 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 40 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 40 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 40 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 40 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 40 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 40 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 40 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 40 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 40 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 40 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 40 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 40
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup41 : gridArray[41]! = gridRow41 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 41 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 41 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 41 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 41 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 41 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 41 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 41 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 41 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 41 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 41 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 41 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 41
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup42 : gridArray[42]! = gridRow42 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 42 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 42 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 42 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 42 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 42 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 42 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 42 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 42 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 42 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 42 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 42 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 42
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup43 : gridArray[43]! = gridRow43 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 43 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 43 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 43 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 43 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 43 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 43 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 43 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 43 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 43 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 43 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 43 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 43
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup44 : gridArray[44]! = gridRow44 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 44 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 44 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 44 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 44 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 44 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 44 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 44 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 44 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 44 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 44 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 44 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 44
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup45 : gridArray[45]! = gridRow45 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 45 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 45 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 45 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 45 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 45 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 45 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 45 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 45 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 45 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 45 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 45 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 45
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup46 : gridArray[46]! = gridRow46 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 46 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 46 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 46 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 46 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 46 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 46 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 46 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 46 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 46 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 46 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 46 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 46
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

theorem grid_lookup47 : gridArray[47]! = gridRow47 := by
  rw [grid_array_eq_prefix]
  rw [gridPrefix13, lookup_left gridPrefix12 gridChunk13 47 (by rw [grid_prefix_size12] <;> decide)]
  rw [gridPrefix12, lookup_left gridPrefix11 gridChunk12 47 (by rw [grid_prefix_size11] <;> decide)]
  rw [gridPrefix11, lookup_left gridPrefix10 gridChunk11 47 (by rw [grid_prefix_size10] <;> decide)]
  rw [gridPrefix10, lookup_left gridPrefix9 gridChunk10 47 (by rw [grid_prefix_size9] <;> decide)]
  rw [gridPrefix9, lookup_left gridPrefix8 gridChunk9 47 (by rw [grid_prefix_size8] <;> decide)]
  rw [gridPrefix8, lookup_left gridPrefix7 gridChunk8 47 (by rw [grid_prefix_size7] <;> decide)]
  rw [gridPrefix7, lookup_left gridPrefix6 gridChunk7 47 (by rw [grid_prefix_size6] <;> decide)]
  rw [gridPrefix6, lookup_left gridPrefix5 gridChunk6 47 (by rw [grid_prefix_size5] <;> decide)]
  rw [gridPrefix5, lookup_left gridPrefix4 gridChunk5 47 (by rw [grid_prefix_size4] <;> decide)]
  rw [gridPrefix4, lookup_left gridPrefix3 gridChunk4 47 (by rw [grid_prefix_size3] <;> decide)]
  rw [gridPrefix3, lookup_left gridPrefix2 gridChunk3 47 (by rw [grid_prefix_size2] <;> decide)]
  rw [gridPrefix2, lookup_right gridPrefix1 gridChunk2 47
    (by rw [grid_prefix_size1] <;> decide)
    (by rw [grid_prefix_size1, grid_chunk_size2] <;> decide), grid_prefix_size1]
  rfl

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.grid_lookup32
