import ElevenSquare.Tasks.T01.Handoff.Groups.G000.Support
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.MaskBridge
import ElevenSquare.Tasks.T01.Handoff.CaseChunkLookup
import ElevenSquare.Tasks.T01.Handoff.Inventory

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G000
open ElevenSquare.Pending
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def indices00 : List ℕ := [3, 58, 62]
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

def indices01 : List ℕ := [65, 68, 69]
theorem finite01 : ∀ n ∈ indices01, 64 ≤ n ∧ n < 128 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk1[n-64]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk1[n-64]!))) := by
  decide
theorem support01 (k : Fin 2184) (hk : k.val ∈ indices01) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite01 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk01 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices02 : List ℕ := [128, 132, 135, 138, 139]
theorem finite02 : ∀ n ∈ indices02, 128 ≤ n ∧ n < 192 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk2[n-128]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk2[n-128]!))) := by
  decide
theorem support02 (k : Fin 2184) (hk : k.val ∈ indices02) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite02 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk02 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices03 : List ℕ := [197, 200, 203, 204, 206, 209, 210, 212, 213, 215]
theorem finite03 : ∀ n ∈ indices03, 192 ≤ n ∧ n < 256 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk3[n-192]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk3[n-192]!))) := by
  decide
theorem support03 (k : Fin 2184) (hk : k.val ∈ indices03) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite03 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk03 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices04 : List ℕ := [310]
theorem finite04 : ∀ n ∈ indices04, 256 ≤ n ∧ n < 320 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk4[n-256]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk4[n-256]!))) := by
  decide
theorem support04 (k : Fin 2184) (hk : k.val ∈ indices04) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite04 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk04 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices08 : List ℕ := [517]
theorem finite08 : ∀ n ∈ indices08, 512 ≤ n ∧ n < 576 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk8[n-512]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk8[n-512]!))) := by
  decide
theorem support08 (k : Fin 2184) (hk : k.val ∈ indices08) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite08 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk08 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices10 : List ℕ := [685, 700]
theorem finite10 : ∀ n ∈ indices10, 640 ≤ n ∧ n < 704 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk10[n-640]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk10[n-640]!))) := by
  decide
theorem support10 (k : Fin 2184) (hk : k.val ∈ indices10) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite10 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk10 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices11 : List ℕ := [712, 715, 766]
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

def indices12 : List ℕ := [770, 773, 776, 777, 822]
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

def indices13 : List ℕ := [834, 837, 840, 841, 843, 846, 847, 849, 850, 852, 886, 889, 892, 893, 895]
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

def indices14 : List ℕ := [898, 899, 901, 902, 904, 937, 940, 941, 943, 944, 946, 947, 948, 950]
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

def indices15 : List ℕ := [980, 994, 1005]
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

def indices16 : List ℕ := [1072, 1085]
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

def indices17 : List ℕ := [1095, 1140, 1149]
theorem finite17 : ∀ n ∈ indices17, 1088 ≤ n ∧ n < 1152 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk17[n-1088]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk17[n-1088]!))) := by
  decide
theorem support17 (k : Fin 2184) (hk : k.val ∈ indices17) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite17 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk17 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices18 : List ℕ := [1152]
theorem finite18 : ∀ n ∈ indices18, 1152 ≤ n ∧ n < 1216 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk18[n-1152]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk18[n-1152]!))) := by
  decide
theorem support18 (k : Fin 2184) (hk : k.val ∈ indices18) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite18 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk18 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices25 : List ℕ := [1655]
theorem finite25 : ∀ n ∈ indices25, 1600 ≤ n ∧ n < 1664 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk25[n-1600]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk25[n-1600]!))) := by
  decide
theorem support25 (k : Fin 2184) (hk : k.val ∈ indices25) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite25 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk25 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices27 : List ℕ := [1763, 1772, 1778]
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

def indices28 : List ℕ := [1819, 1827, 1832, 1855]
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

def indices29 : List ℕ := [1859, 1860, 1881, 1888, 1892, 1913, 1916, 1917]
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

def indices30 : List ℕ := [1923, 1926, 1927, 1930]
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

def indices31 : List ℕ := [2004, 2007, 2009, 2011, 2034, 2038, 2040, 2042, 2043, 2045, 2046]
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

def indices32 : List ℕ := [2059, 2061, 2063, 2064, 2066, 2067, 2079, 2081, 2082, 2083, 2096, 2101]
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

def indices33 : List ℕ := [2124, 2128, 2138, 2140, 2142, 2144, 2145, 2147, 2150, 2153, 2154, 2156]
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

def indices : List ℕ := indices00 ++ indices01 ++ indices02 ++ indices03 ++ indices04 ++ indices08 ++ indices10 ++ indices11 ++ indices12 ++ indices13 ++ indices14 ++ indices15 ++ indices16 ++ indices17 ++ indices18 ++ indices25 ++ indices27 ++ indices28 ++ indices29 ++ indices30 ++ indices31 ++ indices32 ++ indices33
theorem indices_eq : indices = groupCases (0 : Group) := by decide

theorem public_support (k : Fin 2184) (hk : k.val ∈ groupCases (0 : Group)) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have hi : k.val ∈ indices := by rw [indices_eq]; exact hk
  simp only [indices, List.mem_append, or_assoc] at hi
  rcases hi with h00 | h01 | h02 | h03 | h04 | h08 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h25 | h27 | h28 | h29 | h30 | h31 | h32 | h33
  · exact support00 k h00
  · exact support01 k h01
  · exact support02 k h02
  · exact support03 k h03
  · exact support04 k h04
  · exact support08 k h08
  · exact support10 k h10
  · exact support11 k h11
  · exact support12 k h12
  · exact support13 k h13
  · exact support14 k h14
  · exact support15 k h15
  · exact support16 k h16
  · exact support17 k h17
  · exact support18 k h18
  · exact support25 k h25
  · exact support27 k h27
  · exact support28 k h28
  · exact support29 k h29
  · exact support30 k h30
  · exact support31 k h31
  · exact support32 k h32
  · exact support33 k h33

theorem exclusion_of_capture (hcap : SupportCapture)
    (k : Fin 2184) (hk : k.val ∈ groupCases (0 : Group))
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P (caseMask k)) : False :=
  exclusion_of_support_or_halfTurn hcap (caseMask k) (public_support k hk) P hc ho

end ElevenSquare.Tasks.T01.Handoff.Groups.G000
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G000.public_support
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G000.exclusion_of_capture
