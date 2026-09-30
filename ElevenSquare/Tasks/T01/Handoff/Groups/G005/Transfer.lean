import ElevenSquare.Tasks.T01.Handoff.Groups.G005.Support
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.MaskBridge
import ElevenSquare.Tasks.T01.Handoff.CaseChunkLookup
import ElevenSquare.Tasks.T01.Handoff.Inventory

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005
open ElevenSquare.Pending
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def indices00 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]
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

def indices01 : List ℕ := [126, 127]
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

def indices02 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
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

def indices03 : List ℕ := [192, 193, 194, 195, 230, 252, 253, 254, 255]
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

def indices05 : List ℕ := [320, 321, 356, 378, 379, 380, 381, 382, 383]
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

def indices06 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433]
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

def indices07 : List ℕ := [448, 453, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]
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

def indices08 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 563]
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

def indices09 : List ℕ := [584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638]
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

def indices11 : List ℕ := [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759]
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

def indices : List ℕ := indices00 ++ indices01 ++ indices02 ++ indices03 ++ indices04 ++ indices05 ++ indices06 ++ indices07 ++ indices08 ++ indices09 ++ indices10 ++ indices11
theorem indices_eq : indices = groupCases (5 : Group) := by decide

theorem public_support (k : Fin 2184) (hk : k.val ∈ groupCases (5 : Group)) :
    support ⊆ caseMask k ∨ support ⊆ halfTurnMask (caseMask k) := by
  have hi : k.val ∈ indices := by rw [indices_eq]; exact hk
  simp only [indices, List.mem_append, or_assoc] at hi
  rcases hi with h00 | h01 | h02 | h03 | h04 | h05 | h06 | h07 | h08 | h09 | h10 | h11
  · exact support00 k h00
  · exact support01 k h01
  · exact support02 k h02
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
    (k : Fin 2184) (hk : k.val ∈ groupCases (5 : Group))
    (P : Packing 11 coverCap) (hc : IsCharted P) (ho : Occupies P (caseMask k)) : False :=
  exclusion_of_support_or_halfTurn hcap (caseMask k) (public_support k hk) P hc ho

end ElevenSquare.Tasks.T01.Handoff.Groups.G005
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.public_support
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.exclusion_of_capture
