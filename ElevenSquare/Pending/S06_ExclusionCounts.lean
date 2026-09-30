import ElevenSquare.Pending.S06_ExclusionCountChunks0
import ElevenSquare.Pending.S06_ExclusionCountChunks1
import ElevenSquare.Pending.S06_ExclusionCountChunks2
import ElevenSquare.Pending.S06_ExclusionCountChunks3
import ElevenSquare.Pending.S06_ExclusionCountChunks4
import ElevenSquare.Pending.S06_ExclusionCountChunks5
import ElevenSquare.Pending.S06_ExclusionCountChunks6
import ElevenSquare.Pending.S06_ExclusionCountChunks7
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem baseline_prefix1 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1).toList 128 0 127 := by
  rw [array_toList_append]
  exact baseline_block0.append baseline_block1 (by decide)
theorem baseline_prefix2 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2).toList 192 0 191 := by
  rw [array_toList_append]
  exact baseline_prefix1.append baseline_block2 (by decide)
theorem baseline_prefix3 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3).toList 256 0 260 := by
  rw [array_toList_append]
  exact baseline_prefix2.append baseline_block3 (by decide)
theorem baseline_prefix4 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4).toList 320 0 324 := by
  rw [array_toList_append]
  exact baseline_prefix3.append baseline_block4 (by decide)
theorem baseline_prefix5 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5).toList 384 0 388 := by
  rw [array_toList_append]
  exact baseline_prefix4.append baseline_block5 (by decide)
theorem baseline_prefix6 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6).toList 448 0 454 := by
  rw [array_toList_append]
  exact baseline_prefix5.append baseline_block6 (by decide)
theorem baseline_prefix7 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7).toList 512 0 520 := by
  rw [array_toList_append]
  exact baseline_prefix6.append baseline_block7 (by decide)
theorem baseline_prefix8 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8).toList 576 0 584 := by
  rw [array_toList_append]
  exact baseline_prefix7.append baseline_block8 (by decide)
theorem baseline_prefix9 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9).toList 640 0 653 := by
  rw [array_toList_append]
  exact baseline_prefix8.append baseline_block9 (by decide)
theorem baseline_prefix10 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10).toList 704 0 723 := by
  rw [array_toList_append]
  exact baseline_prefix9.append baseline_block10 (by decide)
theorem baseline_prefix11 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11).toList 768 0 790 := by
  rw [array_toList_append]
  exact baseline_prefix10.append baseline_block11 (by decide)
theorem baseline_prefix12 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12).toList 832 0 855 := by
  rw [array_toList_append]
  exact baseline_prefix11.append baseline_block12 (by decide)
theorem baseline_prefix13 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13).toList 896 0 923 := by
  rw [array_toList_append]
  exact baseline_prefix12.append baseline_block13 (by decide)
theorem baseline_prefix14 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14).toList 960 0 1003 := by
  rw [array_toList_append]
  exact baseline_prefix13.append baseline_block14 (by decide)
theorem baseline_prefix15 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15).toList 1024 0 1080 := by
  rw [array_toList_append]
  exact baseline_prefix14.append baseline_block15 (by decide)
theorem baseline_prefix16 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16).toList 1088 0 1159 := by
  rw [array_toList_append]
  exact baseline_prefix15.append baseline_block16 (by decide)
theorem baseline_prefix17 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17).toList 1152 0 1223 := by
  rw [array_toList_append]
  exact baseline_prefix16.append baseline_block17 (by decide)
theorem baseline_prefix18 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18).toList 1216 0 1305 := by
  rw [array_toList_append]
  exact baseline_prefix17.append baseline_block18 (by decide)
theorem baseline_prefix19 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19).toList 1280 0 1386 := by
  rw [array_toList_append]
  exact baseline_prefix18.append baseline_block19 (by decide)
theorem baseline_prefix20 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19 ++ baselineArrayChunk20).toList 1344 0 1472 := by
  rw [array_toList_append]
  exact baseline_prefix19.append baseline_block20 (by decide)
theorem baseline_prefix21 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19 ++ baselineArrayChunk20 ++ baselineArrayChunk21).toList 1408 0 1547 := by
  rw [array_toList_append]
  exact baseline_prefix20.append baseline_block21 (by decide)
theorem baseline_prefix22 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19 ++ baselineArrayChunk20 ++ baselineArrayChunk21 ++ baselineArrayChunk22).toList 1472 0 1618 := by
  rw [array_toList_append]
  exact baseline_prefix21.append baseline_block22 (by decide)
theorem baseline_prefix23 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19 ++ baselineArrayChunk20 ++ baselineArrayChunk21 ++ baselineArrayChunk22 ++ baselineArrayChunk23).toList 1536 0 1707 := by
  rw [array_toList_append]
  exact baseline_prefix22.append baseline_block23 (by decide)
theorem baseline_prefix24 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19 ++ baselineArrayChunk20 ++ baselineArrayChunk21 ++ baselineArrayChunk22 ++ baselineArrayChunk23 ++ baselineArrayChunk24).toList 1600 0 1779 := by
  rw [array_toList_append]
  exact baseline_prefix23.append baseline_block24 (by decide)
theorem baseline_prefix25 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19 ++ baselineArrayChunk20 ++ baselineArrayChunk21 ++ baselineArrayChunk22 ++ baselineArrayChunk23 ++ baselineArrayChunk24 ++ baselineArrayChunk25).toList 1664 0 1858 := by
  rw [array_toList_append]
  exact baseline_prefix24.append baseline_block25 (by decide)
theorem baseline_prefix26 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19 ++ baselineArrayChunk20 ++ baselineArrayChunk21 ++ baselineArrayChunk22 ++ baselineArrayChunk23 ++ baselineArrayChunk24 ++ baselineArrayChunk25 ++ baselineArrayChunk26).toList 1728 0 1931 := by
  rw [array_toList_append]
  exact baseline_prefix25.append baseline_block26 (by decide)
theorem baseline_prefix27 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19 ++ baselineArrayChunk20 ++ baselineArrayChunk21 ++ baselineArrayChunk22 ++ baselineArrayChunk23 ++ baselineArrayChunk24 ++ baselineArrayChunk25 ++ baselineArrayChunk26 ++ baselineArrayChunk27).toList 1792 0 1997 := by
  rw [array_toList_append]
  exact baseline_prefix26.append baseline_block27 (by decide)
theorem baseline_prefix28 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19 ++ baselineArrayChunk20 ++ baselineArrayChunk21 ++ baselineArrayChunk22 ++ baselineArrayChunk23 ++ baselineArrayChunk24 ++ baselineArrayChunk25 ++ baselineArrayChunk26 ++ baselineArrayChunk27 ++ baselineArrayChunk28).toList 1856 0 2082 := by
  rw [array_toList_append]
  exact baseline_prefix27.append baseline_block28 (by decide)
theorem baseline_prefix29 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19 ++ baselineArrayChunk20 ++ baselineArrayChunk21 ++ baselineArrayChunk22 ++ baselineArrayChunk23 ++ baselineArrayChunk24 ++ baselineArrayChunk25 ++ baselineArrayChunk26 ++ baselineArrayChunk27 ++ baselineArrayChunk28 ++ baselineArrayChunk29).toList 1920 0 2166 := by
  rw [array_toList_append]
  exact baseline_prefix28.append baseline_block29 (by decide)
theorem baseline_prefix30 : Block id (baselineArrayChunk0 ++ baselineArrayChunk1 ++ baselineArrayChunk2 ++ baselineArrayChunk3 ++ baselineArrayChunk4 ++ baselineArrayChunk5 ++ baselineArrayChunk6 ++ baselineArrayChunk7 ++ baselineArrayChunk8 ++ baselineArrayChunk9 ++ baselineArrayChunk10 ++ baselineArrayChunk11 ++ baselineArrayChunk12 ++ baselineArrayChunk13 ++ baselineArrayChunk14 ++ baselineArrayChunk15 ++ baselineArrayChunk16 ++ baselineArrayChunk17 ++ baselineArrayChunk18 ++ baselineArrayChunk19 ++ baselineArrayChunk20 ++ baselineArrayChunk21 ++ baselineArrayChunk22 ++ baselineArrayChunk23 ++ baselineArrayChunk24 ++ baselineArrayChunk25 ++ baselineArrayChunk26 ++ baselineArrayChunk27 ++ baselineArrayChunk28 ++ baselineArrayChunk29 ++ baselineArrayChunk30).toList 1931 0 2181 := by
  rw [array_toList_append]
  exact baseline_prefix29.append baseline_block30 (by decide)
theorem baseline_card : baselineIndices.card = 1931 := baseline_prefix30.card
#print axioms baseline_card
theorem prior_prefix1 : Block id (priorArrayChunk0 ++ priorArrayChunk1).toList 76 221 2183 := by
  rw [array_toList_append]
  exact prior_block0.append prior_block1 (by decide)
theorem prior_card : priorIndices.card = 76 := prior_prefix1.card
#print axioms prior_card
theorem returned_prefix1 : Block id (returnedArrayChunk0 ++ returnedArrayChunk1).toList 128 1145 1887 := by
  rw [array_toList_append]
  exact returned_block0.append returned_block1 (by decide)
theorem returned_prefix2 : Block id (returnedArrayChunk0 ++ returnedArrayChunk1 ++ returnedArrayChunk2).toList 173 1145 2135 := by
  rw [array_toList_append]
  exact returned_prefix1.append returned_block2 (by decide)
theorem returned_card : returnedIndices.card = 173 := returned_prefix2.card
#print axioms returned_card
end ElevenSquare.Pending.ExclusionCounts
