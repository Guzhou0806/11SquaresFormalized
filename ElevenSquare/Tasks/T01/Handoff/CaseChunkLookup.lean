import ElevenSquare.Tasks.T01.Handoff.CaseMaskLookup

namespace ElevenSquare.Tasks.T01.Handoff.CaseChunkLookup
open ElevenSquare.Pending ElevenSquare.Pending.CandidateLookup ElevenSquare.Pending.TupleBounds

theorem chunk00 (k : ℕ) (hlo : 0 ≤ k) (hhi : k < 64) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk0[k - 0]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_left prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; omega)]
  rw [prefix10, lookup_left prefix9 recordedCaseTuplesChunk10 k
    (by rw [size_prefix9]; omega)]
  rw [prefix9, lookup_left prefix8 recordedCaseTuplesChunk9 k
    (by rw [size_prefix8]; omega)]
  rw [prefix8, lookup_left prefix7 recordedCaseTuplesChunk8 k
    (by rw [size_prefix7]; omega)]
  rw [prefix7, lookup_left prefix6 recordedCaseTuplesChunk7 k
    (by rw [size_prefix6]; omega)]
  rw [prefix6, lookup_left prefix5 recordedCaseTuplesChunk6 k
    (by rw [size_prefix5]; omega)]
  rw [prefix5, lookup_left prefix4 recordedCaseTuplesChunk5 k
    (by rw [size_prefix4]; omega)]
  rw [prefix4, lookup_left prefix3 recordedCaseTuplesChunk4 k
    (by rw [size_prefix3]; omega)]
  rw [prefix3, lookup_left prefix2 recordedCaseTuplesChunk3 k
    (by rw [size_prefix2]; omega)]
  rw [prefix2, lookup_left prefix1 recordedCaseTuplesChunk2 k
    (by rw [size_prefix1]; omega)]
  rw [prefix1, lookup_left prefix0 recordedCaseTuplesChunk1 k
    (by rw [size_prefix0]; omega)]
  rfl

theorem chunk01 (k : ℕ) (hlo : 64 ≤ k) (hhi : k < 128) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk1[k - 64]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_left prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; omega)]
  rw [prefix10, lookup_left prefix9 recordedCaseTuplesChunk10 k
    (by rw [size_prefix9]; omega)]
  rw [prefix9, lookup_left prefix8 recordedCaseTuplesChunk9 k
    (by rw [size_prefix8]; omega)]
  rw [prefix8, lookup_left prefix7 recordedCaseTuplesChunk8 k
    (by rw [size_prefix7]; omega)]
  rw [prefix7, lookup_left prefix6 recordedCaseTuplesChunk7 k
    (by rw [size_prefix6]; omega)]
  rw [prefix6, lookup_left prefix5 recordedCaseTuplesChunk6 k
    (by rw [size_prefix5]; omega)]
  rw [prefix5, lookup_left prefix4 recordedCaseTuplesChunk5 k
    (by rw [size_prefix4]; omega)]
  rw [prefix4, lookup_left prefix3 recordedCaseTuplesChunk4 k
    (by rw [size_prefix3]; omega)]
  rw [prefix3, lookup_left prefix2 recordedCaseTuplesChunk3 k
    (by rw [size_prefix2]; omega)]
  rw [prefix2, lookup_left prefix1 recordedCaseTuplesChunk2 k
    (by rw [size_prefix1]; omega)]
  rw [prefix1, lookup_right prefix0 recordedCaseTuplesChunk1 k
    (by rw [size_prefix0]; exact hlo)
    (by rw [size_prefix0, tuple_block1.1]; omega), size_prefix0]

theorem chunk02 (k : ℕ) (hlo : 128 ≤ k) (hhi : k < 192) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk2[k - 128]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_left prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; omega)]
  rw [prefix10, lookup_left prefix9 recordedCaseTuplesChunk10 k
    (by rw [size_prefix9]; omega)]
  rw [prefix9, lookup_left prefix8 recordedCaseTuplesChunk9 k
    (by rw [size_prefix8]; omega)]
  rw [prefix8, lookup_left prefix7 recordedCaseTuplesChunk8 k
    (by rw [size_prefix7]; omega)]
  rw [prefix7, lookup_left prefix6 recordedCaseTuplesChunk7 k
    (by rw [size_prefix6]; omega)]
  rw [prefix6, lookup_left prefix5 recordedCaseTuplesChunk6 k
    (by rw [size_prefix5]; omega)]
  rw [prefix5, lookup_left prefix4 recordedCaseTuplesChunk5 k
    (by rw [size_prefix4]; omega)]
  rw [prefix4, lookup_left prefix3 recordedCaseTuplesChunk4 k
    (by rw [size_prefix3]; omega)]
  rw [prefix3, lookup_left prefix2 recordedCaseTuplesChunk3 k
    (by rw [size_prefix2]; omega)]
  rw [prefix2, lookup_right prefix1 recordedCaseTuplesChunk2 k
    (by rw [size_prefix1]; exact hlo)
    (by rw [size_prefix1, tuple_block2.1]; omega), size_prefix1]

theorem chunk03 (k : ℕ) (hlo : 192 ≤ k) (hhi : k < 256) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk3[k - 192]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_left prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; omega)]
  rw [prefix10, lookup_left prefix9 recordedCaseTuplesChunk10 k
    (by rw [size_prefix9]; omega)]
  rw [prefix9, lookup_left prefix8 recordedCaseTuplesChunk9 k
    (by rw [size_prefix8]; omega)]
  rw [prefix8, lookup_left prefix7 recordedCaseTuplesChunk8 k
    (by rw [size_prefix7]; omega)]
  rw [prefix7, lookup_left prefix6 recordedCaseTuplesChunk7 k
    (by rw [size_prefix6]; omega)]
  rw [prefix6, lookup_left prefix5 recordedCaseTuplesChunk6 k
    (by rw [size_prefix5]; omega)]
  rw [prefix5, lookup_left prefix4 recordedCaseTuplesChunk5 k
    (by rw [size_prefix4]; omega)]
  rw [prefix4, lookup_left prefix3 recordedCaseTuplesChunk4 k
    (by rw [size_prefix3]; omega)]
  rw [prefix3, lookup_right prefix2 recordedCaseTuplesChunk3 k
    (by rw [size_prefix2]; exact hlo)
    (by rw [size_prefix2, tuple_block3.1]; omega), size_prefix2]

theorem chunk04 (k : ℕ) (hlo : 256 ≤ k) (hhi : k < 320) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk4[k - 256]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_left prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; omega)]
  rw [prefix10, lookup_left prefix9 recordedCaseTuplesChunk10 k
    (by rw [size_prefix9]; omega)]
  rw [prefix9, lookup_left prefix8 recordedCaseTuplesChunk9 k
    (by rw [size_prefix8]; omega)]
  rw [prefix8, lookup_left prefix7 recordedCaseTuplesChunk8 k
    (by rw [size_prefix7]; omega)]
  rw [prefix7, lookup_left prefix6 recordedCaseTuplesChunk7 k
    (by rw [size_prefix6]; omega)]
  rw [prefix6, lookup_left prefix5 recordedCaseTuplesChunk6 k
    (by rw [size_prefix5]; omega)]
  rw [prefix5, lookup_left prefix4 recordedCaseTuplesChunk5 k
    (by rw [size_prefix4]; omega)]
  rw [prefix4, lookup_right prefix3 recordedCaseTuplesChunk4 k
    (by rw [size_prefix3]; exact hlo)
    (by rw [size_prefix3, tuple_block4.1]; omega), size_prefix3]

theorem chunk05 (k : ℕ) (hlo : 320 ≤ k) (hhi : k < 384) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk5[k - 320]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_left prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; omega)]
  rw [prefix10, lookup_left prefix9 recordedCaseTuplesChunk10 k
    (by rw [size_prefix9]; omega)]
  rw [prefix9, lookup_left prefix8 recordedCaseTuplesChunk9 k
    (by rw [size_prefix8]; omega)]
  rw [prefix8, lookup_left prefix7 recordedCaseTuplesChunk8 k
    (by rw [size_prefix7]; omega)]
  rw [prefix7, lookup_left prefix6 recordedCaseTuplesChunk7 k
    (by rw [size_prefix6]; omega)]
  rw [prefix6, lookup_left prefix5 recordedCaseTuplesChunk6 k
    (by rw [size_prefix5]; omega)]
  rw [prefix5, lookup_right prefix4 recordedCaseTuplesChunk5 k
    (by rw [size_prefix4]; exact hlo)
    (by rw [size_prefix4, tuple_block5.1]; omega), size_prefix4]

theorem chunk06 (k : ℕ) (hlo : 384 ≤ k) (hhi : k < 448) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk6[k - 384]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_left prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; omega)]
  rw [prefix10, lookup_left prefix9 recordedCaseTuplesChunk10 k
    (by rw [size_prefix9]; omega)]
  rw [prefix9, lookup_left prefix8 recordedCaseTuplesChunk9 k
    (by rw [size_prefix8]; omega)]
  rw [prefix8, lookup_left prefix7 recordedCaseTuplesChunk8 k
    (by rw [size_prefix7]; omega)]
  rw [prefix7, lookup_left prefix6 recordedCaseTuplesChunk7 k
    (by rw [size_prefix6]; omega)]
  rw [prefix6, lookup_right prefix5 recordedCaseTuplesChunk6 k
    (by rw [size_prefix5]; exact hlo)
    (by rw [size_prefix5, tuple_block6.1]; omega), size_prefix5]

theorem chunk07 (k : ℕ) (hlo : 448 ≤ k) (hhi : k < 512) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk7[k - 448]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_left prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; omega)]
  rw [prefix10, lookup_left prefix9 recordedCaseTuplesChunk10 k
    (by rw [size_prefix9]; omega)]
  rw [prefix9, lookup_left prefix8 recordedCaseTuplesChunk9 k
    (by rw [size_prefix8]; omega)]
  rw [prefix8, lookup_left prefix7 recordedCaseTuplesChunk8 k
    (by rw [size_prefix7]; omega)]
  rw [prefix7, lookup_right prefix6 recordedCaseTuplesChunk7 k
    (by rw [size_prefix6]; exact hlo)
    (by rw [size_prefix6, tuple_block7.1]; omega), size_prefix6]

theorem chunk08 (k : ℕ) (hlo : 512 ≤ k) (hhi : k < 576) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk8[k - 512]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_left prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; omega)]
  rw [prefix10, lookup_left prefix9 recordedCaseTuplesChunk10 k
    (by rw [size_prefix9]; omega)]
  rw [prefix9, lookup_left prefix8 recordedCaseTuplesChunk9 k
    (by rw [size_prefix8]; omega)]
  rw [prefix8, lookup_right prefix7 recordedCaseTuplesChunk8 k
    (by rw [size_prefix7]; exact hlo)
    (by rw [size_prefix7, tuple_block8.1]; omega), size_prefix7]

theorem chunk09 (k : ℕ) (hlo : 576 ≤ k) (hhi : k < 640) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk9[k - 576]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_left prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; omega)]
  rw [prefix10, lookup_left prefix9 recordedCaseTuplesChunk10 k
    (by rw [size_prefix9]; omega)]
  rw [prefix9, lookup_right prefix8 recordedCaseTuplesChunk9 k
    (by rw [size_prefix8]; exact hlo)
    (by rw [size_prefix8, tuple_block9.1]; omega), size_prefix8]

theorem chunk10 (k : ℕ) (hlo : 640 ≤ k) (hhi : k < 704) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk10[k - 640]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_left prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; omega)]
  rw [prefix10, lookup_right prefix9 recordedCaseTuplesChunk10 k
    (by rw [size_prefix9]; exact hlo)
    (by rw [size_prefix9, tuple_block10.1]; omega), size_prefix9]

theorem chunk11 (k : ℕ) (hlo : 704 ≤ k) (hhi : k < 768) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk11[k - 704]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_left prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; omega)]
  rw [prefix11, lookup_right prefix10 recordedCaseTuplesChunk11 k
    (by rw [size_prefix10]; exact hlo)
    (by rw [size_prefix10, tuple_block11.1]; omega), size_prefix10]

theorem chunk12 (k : ℕ) (hlo : 768 ≤ k) (hhi : k < 832) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk12[k - 768]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_left prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; omega)]
  rw [prefix12, lookup_right prefix11 recordedCaseTuplesChunk12 k
    (by rw [size_prefix11]; exact hlo)
    (by rw [size_prefix11, tuple_block12.1]; omega), size_prefix11]

theorem chunk13 (k : ℕ) (hlo : 832 ≤ k) (hhi : k < 896) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk13[k - 832]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_left prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; omega)]
  rw [prefix13, lookup_right prefix12 recordedCaseTuplesChunk13 k
    (by rw [size_prefix12]; exact hlo)
    (by rw [size_prefix12, tuple_block13.1]; omega), size_prefix12]

theorem chunk14 (k : ℕ) (hlo : 896 ≤ k) (hhi : k < 960) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk14[k - 896]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_left prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; omega)]
  rw [prefix14, lookup_right prefix13 recordedCaseTuplesChunk14 k
    (by rw [size_prefix13]; exact hlo)
    (by rw [size_prefix13, tuple_block14.1]; omega), size_prefix13]

theorem chunk15 (k : ℕ) (hlo : 960 ≤ k) (hhi : k < 1024) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk15[k - 960]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_left prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; omega)]
  rw [prefix15, lookup_right prefix14 recordedCaseTuplesChunk15 k
    (by rw [size_prefix14]; exact hlo)
    (by rw [size_prefix14, tuple_block15.1]; omega), size_prefix14]

theorem chunk16 (k : ℕ) (hlo : 1024 ≤ k) (hhi : k < 1088) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk16[k - 1024]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_left prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; omega)]
  rw [prefix16, lookup_right prefix15 recordedCaseTuplesChunk16 k
    (by rw [size_prefix15]; exact hlo)
    (by rw [size_prefix15, tuple_block16.1]; omega), size_prefix15]

theorem chunk17 (k : ℕ) (hlo : 1088 ≤ k) (hhi : k < 1152) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk17[k - 1088]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_left prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; omega)]
  rw [prefix17, lookup_right prefix16 recordedCaseTuplesChunk17 k
    (by rw [size_prefix16]; exact hlo)
    (by rw [size_prefix16, tuple_block17.1]; omega), size_prefix16]

theorem chunk18 (k : ℕ) (hlo : 1152 ≤ k) (hhi : k < 1216) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk18[k - 1152]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_left prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; omega)]
  rw [prefix18, lookup_right prefix17 recordedCaseTuplesChunk18 k
    (by rw [size_prefix17]; exact hlo)
    (by rw [size_prefix17, tuple_block18.1]; omega), size_prefix17]

theorem chunk19 (k : ℕ) (hlo : 1216 ≤ k) (hhi : k < 1280) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk19[k - 1216]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_left prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; omega)]
  rw [prefix19, lookup_right prefix18 recordedCaseTuplesChunk19 k
    (by rw [size_prefix18]; exact hlo)
    (by rw [size_prefix18, tuple_block19.1]; omega), size_prefix18]

theorem chunk20 (k : ℕ) (hlo : 1280 ≤ k) (hhi : k < 1344) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk20[k - 1280]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_left prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; omega)]
  rw [prefix20, lookup_right prefix19 recordedCaseTuplesChunk20 k
    (by rw [size_prefix19]; exact hlo)
    (by rw [size_prefix19, tuple_block20.1]; omega), size_prefix19]

theorem chunk21 (k : ℕ) (hlo : 1344 ≤ k) (hhi : k < 1408) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk21[k - 1344]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_left prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; omega)]
  rw [prefix21, lookup_right prefix20 recordedCaseTuplesChunk21 k
    (by rw [size_prefix20]; exact hlo)
    (by rw [size_prefix20, tuple_block21.1]; omega), size_prefix20]

theorem chunk22 (k : ℕ) (hlo : 1408 ≤ k) (hhi : k < 1472) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk22[k - 1408]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_left prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; omega)]
  rw [prefix22, lookup_right prefix21 recordedCaseTuplesChunk22 k
    (by rw [size_prefix21]; exact hlo)
    (by rw [size_prefix21, tuple_block22.1]; omega), size_prefix21]

theorem chunk23 (k : ℕ) (hlo : 1472 ≤ k) (hhi : k < 1536) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk23[k - 1472]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_left prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; omega)]
  rw [prefix23, lookup_right prefix22 recordedCaseTuplesChunk23 k
    (by rw [size_prefix22]; exact hlo)
    (by rw [size_prefix22, tuple_block23.1]; omega), size_prefix22]

theorem chunk24 (k : ℕ) (hlo : 1536 ≤ k) (hhi : k < 1600) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk24[k - 1536]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_left prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; omega)]
  rw [prefix24, lookup_right prefix23 recordedCaseTuplesChunk24 k
    (by rw [size_prefix23]; exact hlo)
    (by rw [size_prefix23, tuple_block24.1]; omega), size_prefix23]

theorem chunk25 (k : ℕ) (hlo : 1600 ≤ k) (hhi : k < 1664) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk25[k - 1600]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_left prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; omega)]
  rw [prefix25, lookup_right prefix24 recordedCaseTuplesChunk25 k
    (by rw [size_prefix24]; exact hlo)
    (by rw [size_prefix24, tuple_block25.1]; omega), size_prefix24]

theorem chunk26 (k : ℕ) (hlo : 1664 ≤ k) (hhi : k < 1728) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk26[k - 1664]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_left prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; omega)]
  rw [prefix26, lookup_right prefix25 recordedCaseTuplesChunk26 k
    (by rw [size_prefix25]; exact hlo)
    (by rw [size_prefix25, tuple_block26.1]; omega), size_prefix25]

theorem chunk27 (k : ℕ) (hlo : 1728 ≤ k) (hhi : k < 1792) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk27[k - 1728]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_left prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; omega)]
  rw [prefix27, lookup_right prefix26 recordedCaseTuplesChunk27 k
    (by rw [size_prefix26]; exact hlo)
    (by rw [size_prefix26, tuple_block27.1]; omega), size_prefix26]

theorem chunk28 (k : ℕ) (hlo : 1792 ≤ k) (hhi : k < 1856) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk28[k - 1792]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_left prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; omega)]
  rw [prefix28, lookup_right prefix27 recordedCaseTuplesChunk28 k
    (by rw [size_prefix27]; exact hlo)
    (by rw [size_prefix27, tuple_block28.1]; omega), size_prefix27]

theorem chunk29 (k : ℕ) (hlo : 1856 ≤ k) (hhi : k < 1920) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk29[k - 1856]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_left prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; omega)]
  rw [prefix29, lookup_right prefix28 recordedCaseTuplesChunk29 k
    (by rw [size_prefix28]; exact hlo)
    (by rw [size_prefix28, tuple_block29.1]; omega), size_prefix28]

theorem chunk30 (k : ℕ) (hlo : 1920 ≤ k) (hhi : k < 1984) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk30[k - 1920]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_left prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; omega)]
  rw [prefix30, lookup_right prefix29 recordedCaseTuplesChunk30 k
    (by rw [size_prefix29]; exact hlo)
    (by rw [size_prefix29, tuple_block30.1]; omega), size_prefix29]

theorem chunk31 (k : ℕ) (hlo : 1984 ≤ k) (hhi : k < 2048) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk31[k - 1984]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_left prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; omega)]
  rw [prefix31, lookup_right prefix30 recordedCaseTuplesChunk31 k
    (by rw [size_prefix30]; exact hlo)
    (by rw [size_prefix30, tuple_block31.1]; omega), size_prefix30]

theorem chunk32 (k : ℕ) (hlo : 2048 ≤ k) (hhi : k < 2112) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk32[k - 2048]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_left prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; omega)]
  rw [prefix32, lookup_right prefix31 recordedCaseTuplesChunk32 k
    (by rw [size_prefix31]; exact hlo)
    (by rw [size_prefix31, tuple_block32.1]; omega), size_prefix31]

theorem chunk33 (k : ℕ) (hlo : 2112 ≤ k) (hhi : k < 2176) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk33[k - 2112]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_left prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; omega)]
  rw [prefix33, lookup_right prefix32 recordedCaseTuplesChunk33 k
    (by rw [size_prefix32]; exact hlo)
    (by rw [size_prefix32, tuple_block33.1]; omega), size_prefix32]

theorem chunk34 (k : ℕ) (hlo : 2176 ≤ k) (hhi : k < 2184) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk34[k - 2176]! := by
  rw [recorded_eq_prefix]
  rw [prefix34, lookup_right prefix33 recordedCaseTuplesChunk34 k
    (by rw [size_prefix33]; exact hlo)
    (by rw [size_prefix33, tuple_block34.1]; omega), size_prefix33]

end ElevenSquare.Tasks.T01.Handoff.CaseChunkLookup
#print axioms ElevenSquare.Tasks.T01.Handoff.CaseChunkLookup.chunk00
#print axioms ElevenSquare.Tasks.T01.Handoff.CaseChunkLookup.chunk34
