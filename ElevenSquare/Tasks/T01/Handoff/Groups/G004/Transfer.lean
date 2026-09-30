import ElevenSquare.Tasks.T01.Handoff.Groups.G004.Support
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.MaskBridge
import ElevenSquare.Tasks.T01.Handoff.CaseChunkLookup
import ElevenSquare.Tasks.T01.Handoff.Inventory

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004
open ElevenSquare.Pending
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def indices00 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
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

def indices01 : List ℕ := [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125]
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

def indices03 : List ℕ := [245, 252, 253, 254, 255]
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

def indices04 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]
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

def indices05 : List ℕ := [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377]
theorem finite05 : ∀ n ∈ indices05, 320 ≤ n ∧ n < 384 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk5[n-320]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk5[n-320]!))) := by
  decide
theorem support05 (k : Fin 2184) (hk : k.val ∈ indices05) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite05 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk05 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices06 : List ℕ := [427]
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

def indices07 : List ℕ := [448, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]
theorem finite07 : ∀ n ∈ indices07, 448 ≤ n ∧ n < 512 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk7[n-448]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk7[n-448]!))) := by
  decide
theorem support07 (k : Fin 2184) (hk : k.val ∈ indices07) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite07 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk07 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices08 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]
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

def indices09 : List ℕ := [576, 577, 578, 579, 580, 581, 582, 583, 633]
theorem finite09 : ∀ n ∈ indices09, 576 ≤ n ∧ n < 640 ∧
    (support ⊆ G007.tupleMask (recordedCaseTuplesChunk9[n-576]!) ∨
      support ⊆ halfTurnMask (G007.tupleMask (recordedCaseTuplesChunk9[n-576]!))) := by
  decide
theorem support09 (k : Fin 2184) (hk : k.val ∈ indices09) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have h := finite09 k.val hk
  have he := G007.case_mask_of_recorded_case k _ (CaseChunkLookup.chunk09 k.val h.1 h.2.1)
  rw [he]
  exact h.2.2

def indices10 : List ℕ := [653, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703]
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

def indices11 : List ℕ := [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737]
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

def indices : List ℕ := indices00 ++ indices01 ++ indices03 ++ indices04 ++ indices05 ++ indices06 ++ indices07 ++ indices08 ++ indices09 ++ indices10 ++ indices11
theorem indices_eq : indices = groupCases (4 : Group) := by decide

theorem public_support (k : Fin 2184) (hk : k.val ∈ groupCases (4 : Group)) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have hi : k.val ∈ indices := by rw [indices_eq]; exact hk
  simp only [indices, List.mem_append, or_assoc] at hi
  rcases hi with h00 | h01 | h03 | h04 | h05 | h06 | h07 | h08 | h09 | h10 | h11
  · exact support00 k h00
  · exact support01 k h01
  · exact support03 k h03
  · exact support04 k h04
  · exact support05 k h05
  · exact support06 k h06
  · exact support07 k h07
  · exact support08 k h08
  · exact support09 k h09
  · exact support10 k h10
  · exact support11 k h11

theorem exclusion_of_capture (hcap : SupportCapture)
    (k : Fin 2184) (hk : k.val ∈ groupCases (4 : Group))
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P (caseMask k)) : False :=
  exclusion_of_support_or_halfTurn hcap (caseMask k) (public_support k hk) P hc ho

end ElevenSquare.Tasks.T01.Handoff.Groups.G004
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.public_support
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.exclusion_of_capture
