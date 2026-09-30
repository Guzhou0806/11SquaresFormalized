import ElevenSquare.Pending.S07_BanCountChunks0
import ElevenSquare.Pending.S07_BanCountChunks1
import ElevenSquare.Pending.S07_BanCountChunks2
import ElevenSquare.Pending.S07_BanCountChunks3
import ElevenSquare.Pending.S07_BanCountChunks4

namespace ElevenSquare.Pending
open OrderedData

theorem ban_prefix1 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1).toList 128 (9, 12) (8, 58) := by
  rw [array_toList_append]
  exact ban_block0.append ban_block1 (by decide)

theorem ban_prefix2 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2).toList 192 (9, 12) (44, 63) := by
  rw [array_toList_append]
  exact ban_prefix1.append ban_block2 (by decide)

theorem ban_prefix3 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3).toList 256 (9, 12) (51, 70) := by
  rw [array_toList_append]
  exact ban_prefix2.append ban_block3 (by decide)

theorem ban_prefix4 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4).toList 320 (9, 12) (67, 80) := by
  rw [array_toList_append]
  exact ban_prefix3.append ban_block4 (by decide)

theorem ban_prefix5 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5).toList 384 (9, 12) (31, 89) := by
  rw [array_toList_append]
  exact ban_prefix4.append ban_block5 (by decide)

theorem ban_prefix6 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6).toList 448 (9, 12) (38, 96) := by
  rw [array_toList_append]
  exact ban_prefix5.append ban_block6 (by decide)

theorem ban_prefix7 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7).toList 512 (9, 12) (30, 105) := by
  rw [array_toList_append]
  exact ban_prefix6.append ban_block7 (by decide)

theorem ban_prefix8 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8).toList 576 (9, 12) (41, 115) := by
  rw [array_toList_append]
  exact ban_prefix7.append ban_block8 (by decide)

theorem ban_prefix9 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9).toList 640 (9, 12) (56, 128) := by
  rw [array_toList_append]
  exact ban_prefix8.append ban_block9 (by decide)

theorem ban_prefix10 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10).toList 704 (9, 12) (26, 134) := by
  rw [array_toList_append]
  exact ban_prefix9.append ban_block10 (by decide)

theorem ban_prefix11 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11).toList 768 (9, 12) (41, 138) := by
  rw [array_toList_append]
  exact ban_prefix10.append ban_block11 (by decide)

theorem ban_prefix12 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12).toList 832 (9, 12) (80, 144) := by
  rw [array_toList_append]
  exact ban_prefix11.append ban_block12 (by decide)

theorem ban_prefix13 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13).toList 896 (9, 12) (85, 154) := by
  rw [array_toList_append]
  exact ban_prefix12.append ban_block13 (by decide)

theorem ban_prefix14 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13 ++ bannedPairArrayChunk14).toList 960 (9, 12) (89, 163) := by
  rw [array_toList_append]
  exact ban_prefix13.append ban_block14 (by decide)

theorem ban_prefix15 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13 ++ bannedPairArrayChunk14 ++ bannedPairArrayChunk15).toList 1024 (9, 12) (165, 167) := by
  rw [array_toList_append]
  exact ban_prefix14.append ban_block15 (by decide)

theorem ban_prefix16 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13 ++ bannedPairArrayChunk14 ++ bannedPairArrayChunk15 ++ bannedPairArrayChunk16).toList 1088 (9, 12) (91, 172) := by
  rw [array_toList_append]
  exact ban_prefix15.append ban_block16 (by decide)

theorem ban_prefix17 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13 ++ bannedPairArrayChunk14 ++ bannedPairArrayChunk15 ++ bannedPairArrayChunk16 ++ bannedPairArrayChunk17).toList 1152 (9, 12) (157, 178) := by
  rw [array_toList_append]
  exact ban_prefix16.append ban_block17 (by decide)

theorem ban_prefix18 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13 ++ bannedPairArrayChunk14 ++ bannedPairArrayChunk15 ++ bannedPairArrayChunk16 ++ bannedPairArrayChunk17 ++ bannedPairArrayChunk18).toList 1216 (9, 12) (117, 186) := by
  rw [array_toList_append]
  exact ban_prefix17.append ban_block18 (by decide)

theorem ban_prefix19 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13 ++ bannedPairArrayChunk14 ++ bannedPairArrayChunk15 ++ bannedPairArrayChunk16 ++ bannedPairArrayChunk17 ++ bannedPairArrayChunk18 ++ bannedPairArrayChunk19).toList 1280 (9, 12) (158, 190) := by
  rw [array_toList_append]
  exact ban_prefix18.append ban_block19 (by decide)

theorem ban_prefix20 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13 ++ bannedPairArrayChunk14 ++ bannedPairArrayChunk15 ++ bannedPairArrayChunk16 ++ bannedPairArrayChunk17 ++ bannedPairArrayChunk18 ++ bannedPairArrayChunk19 ++ bannedPairArrayChunk20).toList 1344 (9, 12) (153, 195) := by
  rw [array_toList_append]
  exact ban_prefix19.append ban_block20 (by decide)

theorem ban_prefix21 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13 ++ bannedPairArrayChunk14 ++ bannedPairArrayChunk15 ++ bannedPairArrayChunk16 ++ bannedPairArrayChunk17 ++ bannedPairArrayChunk18 ++ bannedPairArrayChunk19 ++ bannedPairArrayChunk20 ++ bannedPairArrayChunk21).toList 1408 (9, 12) (155, 204) := by
  rw [array_toList_append]
  exact ban_prefix20.append ban_block21 (by decide)

theorem ban_prefix22 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13 ++ bannedPairArrayChunk14 ++ bannedPairArrayChunk15 ++ bannedPairArrayChunk16 ++ bannedPairArrayChunk17 ++ bannedPairArrayChunk18 ++ bannedPairArrayChunk19 ++ bannedPairArrayChunk20 ++ bannedPairArrayChunk21 ++ bannedPairArrayChunk22).toList 1472 (9, 12) (193, 209) := by
  rw [array_toList_append]
  exact ban_prefix21.append ban_block22 (by decide)

theorem ban_prefix23 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13 ++ bannedPairArrayChunk14 ++ bannedPairArrayChunk15 ++ bannedPairArrayChunk16 ++ bannedPairArrayChunk17 ++ bannedPairArrayChunk18 ++ bannedPairArrayChunk19 ++ bannedPairArrayChunk20 ++ bannedPairArrayChunk21 ++ bannedPairArrayChunk22 ++ bannedPairArrayChunk23).toList 1536 (9, 12) (166, 215) := by
  rw [array_toList_append]
  exact ban_prefix22.append ban_block23 (by decide)

theorem ban_prefix24 : Block banKey (bannedPairArrayChunk0 ++ bannedPairArrayChunk1 ++ bannedPairArrayChunk2 ++ bannedPairArrayChunk3 ++ bannedPairArrayChunk4 ++ bannedPairArrayChunk5 ++ bannedPairArrayChunk6 ++ bannedPairArrayChunk7 ++ bannedPairArrayChunk8 ++ bannedPairArrayChunk9 ++ bannedPairArrayChunk10 ++ bannedPairArrayChunk11 ++ bannedPairArrayChunk12 ++ bannedPairArrayChunk13 ++ bannedPairArrayChunk14 ++ bannedPairArrayChunk15 ++ bannedPairArrayChunk16 ++ bannedPairArrayChunk17 ++ bannedPairArrayChunk18 ++ bannedPairArrayChunk19 ++ bannedPairArrayChunk20 ++ bannedPairArrayChunk21 ++ bannedPairArrayChunk22 ++ bannedPairArrayChunk23 ++ bannedPairArrayChunk24).toList 1572 (9, 12) (193, 219) := by
  rw [array_toList_append]
  exact ban_prefix23.append ban_block24 (by decide)

theorem recorded_bans_count : bannedPairs.card = 1572 := by
  change bannedPairArray.toList.toFinset.card = 1572
  have h : Block banKey bannedPairArray.toList 1572 (9, 12) (193, 219) := ban_prefix24
  exact h.card

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.recorded_bans_count
