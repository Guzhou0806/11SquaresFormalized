import ElevenSquare.Pending.S06_CaseCheckChunks0
import ElevenSquare.Pending.S06_CaseCheckChunks1
import ElevenSquare.Pending.S06_CaseCheckChunks2
import ElevenSquare.Pending.S06_CaseCheckChunks3
import ElevenSquare.Pending.S06_CaseCheckChunks4
import ElevenSquare.Pending.S06_CaseCheckChunks5
import ElevenSquare.Pending.S06_CaseCheckChunks6
import ElevenSquare.Pending.S06_CaseCheckChunks7
import ElevenSquare.Pending.S06_CaseCheckChunks8
import ElevenSquare.Pending.S06_CaseCheckChunks9
import ElevenSquare.Pending.S06_CaseCheckChunks10
import ElevenSquare.Pending.S06_CaseCheckChunks11
import ElevenSquare.Pending.S06_CaseCheckChunks12
import ElevenSquare.Pending.S06_CaseCheckChunks13
import ElevenSquare.Pending.S06_CaseCheckChunks14
import ElevenSquare.Pending.S06_CaseCheckChunks15
import ElevenSquare.Pending.S06_CaseCheckChunks16
import ElevenSquare.Pending.S06_CaseCheckChunks17
import ElevenSquare.Pending.S06_CaseCheckChunks18
import ElevenSquare.Pending.S06_CaseCheckChunks19
import ElevenSquare.Pending.S06_CaseCheckChunks20
import ElevenSquare.Pending.S06_CaseCheckChunks21
import ElevenSquare.Pending.S06_CaseCheckChunks22
import ElevenSquare.Pending.S06_CaseCheckChunks23
import ElevenSquare.Pending.S06_CaseCheckChunks24
import ElevenSquare.Pending.S06_CaseCheckChunks25
import ElevenSquare.Pending.S06_CaseCheckChunks26
import ElevenSquare.Pending.S06_CaseCheckChunks27
import ElevenSquare.Pending.S06_CaseCheckChunks28
import ElevenSquare.Pending.S06_CaseCheckChunks29
import ElevenSquare.Pending.S06_CaseCheckChunks30
import ElevenSquare.Pending.S06_CaseCheckChunks31
import ElevenSquare.Pending.S06_CaseCheckChunks32
import ElevenSquare.Pending.S06_CaseCheckChunks33
import ElevenSquare.Pending.S06_CaseCheckChunks34
import ElevenSquare.Pending.S06_CaseTableSound
import ElevenSquare.Pending.S06_TupleBounds
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
theorem case_prefix1 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1).toList 128 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12] := by
  rw [array_toList_append]
  exact case_block0.append case_block1 (by decide)
theorem case_prefix2 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2).toList 192 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 3, 4, 5, 7, 11, 12, 13, 14] := by
  rw [array_toList_append]
  exact case_prefix1.append case_block2 (by decide)
theorem case_prefix3 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3).toList 256 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 14] := by
  rw [array_toList_append]
  exact case_prefix2.append case_block3 (by decide)
theorem case_prefix4 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4).toList 320 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 3, 4, 6, 7, 11, 12, 14, 15] := by
  rw [array_toList_append]
  exact case_prefix3.append case_block4 (by decide)
theorem case_prefix5 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5).toList 384 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 3, 4, 7, 8, 9, 10, 12, 14] := by
  rw [array_toList_append]
  exact case_prefix4.append case_block5 (by decide)
theorem case_prefix6 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6).toList 448 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 3, 4, 8, 9, 11, 13, 14, 15] := by
  rw [array_toList_append]
  exact case_prefix5.append case_block6 (by decide)
theorem case_prefix7 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7).toList 512 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 3, 5, 6, 7, 9, 12, 13, 15] := by
  rw [array_toList_append]
  exact case_prefix6.append case_block7 (by decide)
theorem case_prefix8 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8).toList 576 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 3, 5, 6, 9, 11, 12, 13, 15] := by
  rw [array_toList_append]
  exact case_prefix7.append case_block8 (by decide)
theorem case_prefix9 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9).toList 640 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 3, 5, 8, 9, 10, 11, 12, 13] := by
  rw [array_toList_append]
  exact case_prefix8.append case_block9 (by decide)
theorem case_prefix10 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10).toList 704 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 3, 6, 7, 9, 10, 12, 13, 14] := by
  rw [array_toList_append]
  exact case_prefix9.append case_block10 (by decide)
theorem case_prefix11 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11).toList 768 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 14] := by
  rw [array_toList_append]
  exact case_prefix10.append case_block11 (by decide)
theorem case_prefix12 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12).toList 832 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 4, 5, 6, 7, 11, 12, 14, 15] := by
  rw [array_toList_append]
  exact case_prefix11.append case_block12 (by decide)
theorem case_prefix13 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13).toList 896 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 4, 5, 7, 8, 9, 11, 12, 13] := by
  rw [array_toList_append]
  exact case_prefix12.append case_block13 (by decide)
theorem case_prefix14 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14).toList 960 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 4, 6, 7, 8, 9, 10, 11, 14] := by
  rw [array_toList_append]
  exact case_prefix13.append case_block14 (by decide)
theorem case_prefix15 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15).toList 1024 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 4, 6, 8, 10, 11, 12, 14, 15] := by
  rw [array_toList_append]
  exact case_prefix14.append case_block15 (by decide)
theorem case_prefix16 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16).toList 1088 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 5, 6, 7, 9, 10, 11, 14, 15] := by
  rw [array_toList_append]
  exact case_prefix15.append case_block16 (by decide)
theorem case_prefix17 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17).toList 1152 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 2, 6, 7, 8, 10, 11, 12, 14, 15] := by
  rw [array_toList_append]
  exact case_prefix16.append case_block17 (by decide)
theorem case_prefix18 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18).toList 1216 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 3, 4, 5, 6, 7, 10, 11, 12, 14] := by
  rw [array_toList_append]
  exact case_prefix17.append case_block18 (by decide)
theorem case_prefix19 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19).toList 1280 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 3, 4, 5, 7, 8, 9, 10, 13, 14] := by
  rw [array_toList_append]
  exact case_prefix18.append case_block19 (by decide)
theorem case_prefix20 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20).toList 1344 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 3, 4, 6, 7, 8, 9, 10, 14, 15] := by
  rw [array_toList_append]
  exact case_prefix19.append case_block20 (by decide)
theorem case_prefix21 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21).toList 1408 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 3, 4, 7, 9, 10, 11, 12, 13, 14] := by
  rw [array_toList_append]
  exact case_prefix20.append case_block21 (by decide)
theorem case_prefix22 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22).toList 1472 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 3, 5, 7, 8, 9, 10, 11, 13, 14] := by
  rw [array_toList_append]
  exact case_prefix21.append case_block22 (by decide)
theorem case_prefix23 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23).toList 1536 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 4, 5, 6, 7, 9, 10, 11, 14, 15] := by
  rw [array_toList_append]
  exact case_prefix22.append case_block23 (by decide)
theorem case_prefix24 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23 ++ recordedCaseTuplesChunk24).toList 1600 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 1, 5, 6, 7, 9, 10, 11, 12, 13, 15] := by
  rw [array_toList_append]
  exact case_prefix23.append case_block24 (by decide)
theorem case_prefix25 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23 ++ recordedCaseTuplesChunk24 ++ recordedCaseTuplesChunk25).toList 1664 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 2, 3, 4, 5, 6, 8, 9, 10, 11, 14] := by
  rw [array_toList_append]
  exact case_prefix24.append case_block25 (by decide)
theorem case_prefix26 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23 ++ recordedCaseTuplesChunk24 ++ recordedCaseTuplesChunk25 ++ recordedCaseTuplesChunk26).toList 1728 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 2, 3, 4, 5, 7, 9, 10, 12, 13, 14] := by
  rw [array_toList_append]
  exact case_prefix25.append case_block26 (by decide)
theorem case_prefix27 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23 ++ recordedCaseTuplesChunk24 ++ recordedCaseTuplesChunk25 ++ recordedCaseTuplesChunk26 ++ recordedCaseTuplesChunk27).toList 1792 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 2, 3, 4, 7, 8, 9, 10, 11, 12, 15] := by
  rw [array_toList_append]
  exact case_prefix26.append case_block27 (by decide)
theorem case_prefix28 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23 ++ recordedCaseTuplesChunk24 ++ recordedCaseTuplesChunk25 ++ recordedCaseTuplesChunk26 ++ recordedCaseTuplesChunk27 ++ recordedCaseTuplesChunk28).toList 1856 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 2, 3, 6, 7, 8, 9, 10, 11, 13, 14] := by
  rw [array_toList_append]
  exact case_prefix27.append case_block28 (by decide)
theorem case_prefix29 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23 ++ recordedCaseTuplesChunk24 ++ recordedCaseTuplesChunk25 ++ recordedCaseTuplesChunk26 ++ recordedCaseTuplesChunk27 ++ recordedCaseTuplesChunk28 ++ recordedCaseTuplesChunk29).toList 1920 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 2, 4, 7, 8, 9, 10, 11, 12, 13, 14] := by
  rw [array_toList_append]
  exact case_prefix28.append case_block29 (by decide)
theorem case_prefix30 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23 ++ recordedCaseTuplesChunk24 ++ recordedCaseTuplesChunk25 ++ recordedCaseTuplesChunk26 ++ recordedCaseTuplesChunk27 ++ recordedCaseTuplesChunk28 ++ recordedCaseTuplesChunk29 ++ recordedCaseTuplesChunk30).toList 1984 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [0, 3, 5, 6, 7, 8, 9, 10, 11, 13, 14] := by
  rw [array_toList_append]
  exact case_prefix29.append case_block30 (by decide)
theorem case_prefix31 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23 ++ recordedCaseTuplesChunk24 ++ recordedCaseTuplesChunk25 ++ recordedCaseTuplesChunk26 ++ recordedCaseTuplesChunk27 ++ recordedCaseTuplesChunk28 ++ recordedCaseTuplesChunk29 ++ recordedCaseTuplesChunk30 ++ recordedCaseTuplesChunk31).toList 2048 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13] := by
  rw [array_toList_append]
  exact case_prefix30.append case_block31 (by decide)
theorem case_prefix32 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23 ++ recordedCaseTuplesChunk24 ++ recordedCaseTuplesChunk25 ++ recordedCaseTuplesChunk26 ++ recordedCaseTuplesChunk27 ++ recordedCaseTuplesChunk28 ++ recordedCaseTuplesChunk29 ++ recordedCaseTuplesChunk30 ++ recordedCaseTuplesChunk31 ++ recordedCaseTuplesChunk32).toList 2112 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [1, 2, 3, 4, 7, 8, 9, 10, 12, 13, 14] := by
  rw [array_toList_append]
  exact case_prefix31.append case_block32 (by decide)
theorem case_prefix33 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23 ++ recordedCaseTuplesChunk24 ++ recordedCaseTuplesChunk25 ++ recordedCaseTuplesChunk26 ++ recordedCaseTuplesChunk27 ++ recordedCaseTuplesChunk28 ++ recordedCaseTuplesChunk29 ++ recordedCaseTuplesChunk30 ++ recordedCaseTuplesChunk31 ++ recordedCaseTuplesChunk32 ++ recordedCaseTuplesChunk33).toList 2176 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13] := by
  rw [array_toList_append]
  exact case_prefix32.append case_block33 (by decide)
theorem case_prefix34 : Block rowKey (recordedCaseTuplesChunk0 ++ recordedCaseTuplesChunk1 ++ recordedCaseTuplesChunk2 ++ recordedCaseTuplesChunk3 ++ recordedCaseTuplesChunk4 ++ recordedCaseTuplesChunk5 ++ recordedCaseTuplesChunk6 ++ recordedCaseTuplesChunk7 ++ recordedCaseTuplesChunk8 ++ recordedCaseTuplesChunk9 ++ recordedCaseTuplesChunk10 ++ recordedCaseTuplesChunk11 ++ recordedCaseTuplesChunk12 ++ recordedCaseTuplesChunk13 ++ recordedCaseTuplesChunk14 ++ recordedCaseTuplesChunk15 ++ recordedCaseTuplesChunk16 ++ recordedCaseTuplesChunk17 ++ recordedCaseTuplesChunk18 ++ recordedCaseTuplesChunk19 ++ recordedCaseTuplesChunk20 ++ recordedCaseTuplesChunk21 ++ recordedCaseTuplesChunk22 ++ recordedCaseTuplesChunk23 ++ recordedCaseTuplesChunk24 ++ recordedCaseTuplesChunk25 ++ recordedCaseTuplesChunk26 ++ recordedCaseTuplesChunk27 ++ recordedCaseTuplesChunk28 ++ recordedCaseTuplesChunk29 ++ recordedCaseTuplesChunk30 ++ recordedCaseTuplesChunk31 ++ recordedCaseTuplesChunk32 ++ recordedCaseTuplesChunk33 ++ recordedCaseTuplesChunk34).toList 2184 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13] := by
  rw [array_toList_append]
  exact case_prefix33.append case_block34 (by decide)
theorem all_case_rows_good : RowsGood recordedCaseTuples := by
  unfold recordedCaseTuples
  exact (((((((((((((((((((((((((((((((((((show RowsGood recordedCaseTuplesChunk0 from case_good0).append case_good1).append case_good2).append case_good3).append case_good4).append case_good5).append case_good6).append case_good7).append case_good8).append case_good9).append case_good10).append case_good11).append case_good12).append case_good13).append case_good14).append case_good15).append case_good16).append case_good17).append case_good18).append case_good19).append case_good20).append case_good21).append case_good22).append case_good23).append case_good24).append case_good25).append case_good26).append case_good27).append case_good28).append case_good29).append case_good30).append case_good31).append case_good32).append case_good33).append case_good34)
end ElevenSquare.Pending.CaseChecks
namespace ElevenSquare.Pending
open CaseChecks
theorem recorded_cases_exact :
    Function.Injective caseMask ∧ Finset.univ.image caseMask = canonicalMasks := by
  exact table_exact_block recordedCaseTuples _ _ recorded_case_tuple_bounds.1 case_prefix34 all_case_rows_good
end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.recorded_cases_exact
