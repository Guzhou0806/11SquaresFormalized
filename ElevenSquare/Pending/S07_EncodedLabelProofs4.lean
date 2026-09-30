import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup64 : recordedOverlayLabels[64]! = recordedOverlayLabelsChunk2[0]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 64 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 64 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 64 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 64 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 64
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good64 : LabelGood 64 := by
  unfold LabelGood
  rw [label_lookup64]
  decide
theorem label_lookup65 : recordedOverlayLabels[65]! = recordedOverlayLabelsChunk2[1]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 65 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 65 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 65 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 65 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 65
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good65 : LabelGood 65 := by
  unfold LabelGood
  rw [label_lookup65]
  decide
theorem label_lookup66 : recordedOverlayLabels[66]! = recordedOverlayLabelsChunk2[2]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 66 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 66 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 66 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 66 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 66
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good66 : LabelGood 66 := by
  unfold LabelGood
  rw [label_lookup66]
  decide
theorem label_lookup67 : recordedOverlayLabels[67]! = recordedOverlayLabelsChunk2[3]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 67 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 67 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 67 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 67 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 67
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good67 : LabelGood 67 := by
  unfold LabelGood
  rw [label_lookup67]
  decide
theorem label_lookup68 : recordedOverlayLabels[68]! = recordedOverlayLabelsChunk2[4]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 68 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 68 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 68 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 68 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 68
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good68 : LabelGood 68 := by
  unfold LabelGood
  rw [label_lookup68]
  decide
theorem label_lookup69 : recordedOverlayLabels[69]! = recordedOverlayLabelsChunk2[5]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 69 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 69 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 69 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 69 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 69
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good69 : LabelGood 69 := by
  unfold LabelGood
  rw [label_lookup69]
  decide
theorem label_lookup70 : recordedOverlayLabels[70]! = recordedOverlayLabelsChunk2[6]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 70 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 70 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 70 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 70 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 70
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good70 : LabelGood 70 := by
  unfold LabelGood
  rw [label_lookup70]
  decide
theorem label_lookup71 : recordedOverlayLabels[71]! = recordedOverlayLabelsChunk2[7]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 71 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 71 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 71 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 71 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 71
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good71 : LabelGood 71 := by
  unfold LabelGood
  rw [label_lookup71]
  decide
theorem label_lookup72 : recordedOverlayLabels[72]! = recordedOverlayLabelsChunk2[8]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 72 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 72 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 72 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 72 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 72
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good72 : LabelGood 72 := by
  unfold LabelGood
  rw [label_lookup72]
  decide
theorem label_lookup73 : recordedOverlayLabels[73]! = recordedOverlayLabelsChunk2[9]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 73 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 73 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 73 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 73 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 73
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good73 : LabelGood 73 := by
  unfold LabelGood
  rw [label_lookup73]
  decide
theorem label_lookup74 : recordedOverlayLabels[74]! = recordedOverlayLabelsChunk2[10]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 74 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 74 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 74 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 74 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 74
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good74 : LabelGood 74 := by
  unfold LabelGood
  rw [label_lookup74]
  decide
theorem label_lookup75 : recordedOverlayLabels[75]! = recordedOverlayLabelsChunk2[11]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 75 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 75 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 75 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 75 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 75
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good75 : LabelGood 75 := by
  unfold LabelGood
  rw [label_lookup75]
  decide
theorem label_lookup76 : recordedOverlayLabels[76]! = recordedOverlayLabelsChunk2[12]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 76 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 76 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 76 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 76 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 76
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good76 : LabelGood 76 := by
  unfold LabelGood
  rw [label_lookup76]
  decide
theorem label_lookup77 : recordedOverlayLabels[77]! = recordedOverlayLabelsChunk2[13]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 77 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 77 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 77 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 77 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 77
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good77 : LabelGood 77 := by
  unfold LabelGood
  rw [label_lookup77]
  decide
theorem label_lookup78 : recordedOverlayLabels[78]! = recordedOverlayLabelsChunk2[14]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 78 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 78 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 78 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 78 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 78
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good78 : LabelGood 78 := by
  unfold LabelGood
  rw [label_lookup78]
  decide
theorem label_lookup79 : recordedOverlayLabels[79]! = recordedOverlayLabelsChunk2[15]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 79 (by rw [label_prefix_size5]; decide)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 79 (by rw [label_prefix_size4]; decide)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 79 (by rw [label_prefix_size3]; decide)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 79 (by rw [label_prefix_size2]; decide)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 79
    (by rw [label_prefix_size1] <;> decide)
    (by rw [label_prefix_size1, label_chunk_size2] <;> decide), label_prefix_size1]
theorem label_good79 : LabelGood 79 := by
  unfold LabelGood
  rw [label_lookup79]
  decide
theorem labels_range4 : AllRange LabelGood 64 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good64, (List.forall_mem_cons.mpr ⟨label_good65, (List.forall_mem_cons.mpr ⟨label_good66, (List.forall_mem_cons.mpr ⟨label_good67, (List.forall_mem_cons.mpr ⟨label_good68, (List.forall_mem_cons.mpr ⟨label_good69, (List.forall_mem_cons.mpr ⟨label_good70, (List.forall_mem_cons.mpr ⟨label_good71, (List.forall_mem_cons.mpr ⟨label_good72, (List.forall_mem_cons.mpr ⟨label_good73, (List.forall_mem_cons.mpr ⟨label_good74, (List.forall_mem_cons.mpr ⟨label_good75, (List.forall_mem_cons.mpr ⟨label_good76, (List.forall_mem_cons.mpr ⟨label_good77, (List.forall_mem_cons.mpr ⟨label_good78, (List.forall_mem_cons.mpr ⟨label_good79, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range4
