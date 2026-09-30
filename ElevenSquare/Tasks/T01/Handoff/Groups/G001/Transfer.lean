import ElevenSquare.Tasks.T01.Handoff.Groups.G001.Support
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.MaskBridge
import ElevenSquare.Tasks.T01.Handoff.CaseChunkLookup
import ElevenSquare.Tasks.T01.Handoff.Inventory

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G001
open ElevenSquare.Pending
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def indices00 : List ℕ := [1, 6, 11, 12, 13, 14, 21, 26, 27, 28, 29, 36, 37, 38, 39, 46, 47, 48, 49, 50, 51]
theorem finite00 : ∀ n ∈ indices00, 0 ≤ n ∧ n < 64 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk0[n-0]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk0[n-0]!))) := by
  decide
theorem support00 (k : Fin 2184) (hk : k.val ∈ indices00) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite00 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk00 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices06 : List ℕ := [437]
theorem finite06 : ∀ n ∈ indices06, 384 ≤ n ∧ n < 448 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk6[n-384]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk6[n-384]!))) := by
  decide
theorem support06 (k : Fin 2184) (hk : k.val ∈ indices06) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite06 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk06 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices11 : List ℕ := [764]
theorem finite11 : ∀ n ∈ indices11, 704 ≤ n ∧ n < 768 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk11[n-704]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk11[n-704]!))) := by
  decide
theorem support11 (k : Fin 2184) (hk : k.val ∈ indices11) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite11 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk11 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices12 : List ℕ := [769, 770, 771, 772, 779, 780, 781, 782, 789, 790, 791, 792, 793, 794, 799, 800, 801, 802, 809, 810, 811, 812, 813, 814, 819, 820, 821, 822, 823, 824, 829, 830, 831]
theorem finite12 : ∀ n ∈ indices12, 768 ≤ n ∧ n < 832 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk12[n-768]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk12[n-768]!))) := by
  decide
theorem support12 (k : Fin 2184) (hk : k.val ∈ indices12) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite12 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk12 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices13 : List ℕ := [832]
theorem finite13 : ∀ n ∈ indices13, 832 ≤ n ∧ n < 896 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk13[n-832]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk13[n-832]!))) := by
  decide
theorem support13 (k : Fin 2184) (hk : k.val ∈ indices13) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite13 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk13 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices14 : List ℕ := [940]
theorem finite14 : ∀ n ∈ indices14, 896 ≤ n ∧ n < 960 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk14[n-896]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk14[n-896]!))) := by
  decide
theorem support14 (k : Fin 2184) (hk : k.val ∈ indices14) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite14 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk14 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices15 : List ℕ := [1011]
theorem finite15 : ∀ n ∈ indices15, 960 ≤ n ∧ n < 1024 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk15[n-960]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk15[n-960]!))) := by
  decide
theorem support15 (k : Fin 2184) (hk : k.val ∈ indices15) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite15 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk15 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices16 : List ℕ := [1030, 1046]
theorem finite16 : ∀ n ∈ indices16, 1024 ≤ n ∧ n < 1088 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk16[n-1024]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk16[n-1024]!))) := by
  decide
theorem support16 (k : Fin 2184) (hk : k.val ∈ indices16) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite16 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk16 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices20 : List ℕ := [1321]
theorem finite20 : ∀ n ∈ indices20, 1280 ≤ n ∧ n < 1344 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk20[n-1280]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk20[n-1280]!))) := by
  decide
theorem support20 (k : Fin 2184) (hk : k.val ∈ indices20) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite20 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk20 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices21 : List ℕ := [1382, 1397]
theorem finite21 : ∀ n ∈ indices21, 1344 ≤ n ∧ n < 1408 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk21[n-1344]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk21[n-1344]!))) := by
  decide
theorem support21 (k : Fin 2184) (hk : k.val ∈ indices21) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite21 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk21 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices22 : List ℕ := [1409]
theorem finite22 : ∀ n ∈ indices22, 1408 ≤ n ∧ n < 1472 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk22[n-1408]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk22[n-1408]!))) := by
  decide
theorem support22 (k : Fin 2184) (hk : k.val ∈ indices22) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite22 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk22 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices24 : List ℕ := [1545, 1558, 1568, 1573, 1583, 1585]
theorem finite24 : ∀ n ∈ indices24, 1536 ≤ n ∧ n < 1600 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk24[n-1536]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk24[n-1536]!))) := by
  decide
theorem support24 (k : Fin 2184) (hk : k.val ∈ indices24) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite24 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk24 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices27 : List ℕ := [1736, 1782]
theorem finite27 : ∀ n ∈ indices27, 1728 ≤ n ∧ n < 1792 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk27[n-1728]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk27[n-1728]!))) := by
  decide
theorem support27 (k : Fin 2184) (hk : k.val ∈ indices27) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite27 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk27 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices28 : List ℕ := [1792, 1799]
theorem finite28 : ∀ n ∈ indices28, 1792 ≤ n ∧ n < 1856 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk28[n-1792]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk28[n-1792]!))) := by
  decide
theorem support28 (k : Fin 2184) (hk : k.val ∈ indices28) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite28 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk28 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices29 : List ℕ := [1896, 1904, 1909, 1913, 1918, 1919]
theorem finite29 : ∀ n ∈ indices29, 1856 ≤ n ∧ n < 1920 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk29[n-1856]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk29[n-1856]!))) := by
  decide
theorem support29 (k : Fin 2184) (hk : k.val ∈ indices29) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite29 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk29 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices30 : List ℕ := [1959, 1966, 1971, 1974, 1979, 1980]
theorem finite30 : ∀ n ∈ indices30, 1920 ≤ n ∧ n < 1984 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk30[n-1920]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk30[n-1920]!))) := by
  decide
theorem support30 (k : Fin 2184) (hk : k.val ∈ indices30) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite30 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk30 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices31 : List ℕ := [1993, 1998, 1999, 2000, 2002, 2006, 2007, 2008, 2012, 2013, 2014, 2018, 2019, 2020, 2022, 2023, 2024, 2028, 2029, 2030, 2032, 2033, 2034, 2036]
theorem finite31 : ∀ n ∈ indices31, 1984 ≤ n ∧ n < 2048 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk31[n-1984]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk31[n-1984]!))) := by
  decide
theorem support31 (k : Fin 2184) (hk : k.val ∈ indices31) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite31 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk31 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices32 : List ℕ := [2081, 2106, 2110]
theorem finite32 : ∀ n ∈ indices32, 2048 ≤ n ∧ n < 2112 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk32[n-2048]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk32[n-2048]!))) := by
  decide
theorem support32 (k : Fin 2184) (hk : k.val ∈ indices32) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite32 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk32 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices33 : List ℕ := [2139, 2140, 2141, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153]
theorem finite33 : ∀ n ∈ indices33, 2112 ≤ n ∧ n < 2176 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk33[n-2112]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk33[n-2112]!))) := by
  decide
theorem support33 (k : Fin 2184) (hk : k.val ∈ indices33) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite33 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk33 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices : List ℕ := indices00 ++ indices06 ++ indices11 ++ indices12 ++ indices13 ++ indices14 ++ indices15 ++ indices16 ++ indices20 ++ indices21 ++ indices22 ++ indices24 ++ indices27 ++ indices28 ++ indices29 ++ indices30 ++ indices31 ++ indices32 ++ indices33
theorem indices_eq : indices = groupCases (1 : Group) := by decide

theorem public_support (k : Fin 2184) (hk : k.val ∈ groupCases (1 : Group)) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have hi : k.val ∈ indices := by rw [indices_eq]; exact hk
  simp only [indices, List.mem_append, or_assoc] at hi
  rcases hi with h00 | h06 | h11 | h12 | h13 | h14 | h15 | h16 | h20 | h21 | h22 | h24 | h27 | h28 | h29 | h30 | h31 | h32 | h33
  · exact support00 k h00
  · exact support06 k h06
  · exact support11 k h11
  · exact support12 k h12
  · exact support13 k h13
  · exact support14 k h14
  · exact support15 k h15
  · exact support16 k h16
  · exact support20 k h20
  · exact support21 k h21
  · exact support22 k h22
  · exact support24 k h24
  · exact support27 k h27
  · exact support28 k h28
  · exact support29 k h29
  · exact support30 k h30
  · exact support31 k h31
  · exact support32 k h32
  · exact support33 k h33

theorem exclusion_of_capture (hcap : SupportCapture)
    (k : Fin 2184) (hk : k.val ∈ groupCases (1 : Group))
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P (caseMask k)) : False :=
  exclusion_of_support_or_halfTurn hcap (caseMask k) (public_support k hk) P hc ho

end ElevenSquare.Tasks.T01.Handoff.Groups.G001
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G001.public_support
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G001.exclusion_of_capture
