import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 8.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_8_10_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 0 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_10_15 plane_2_0_6 plane_3_0_6 2468704435 56478747583 56887120403
      (by decide) p (plane_1_10_15_sound p h1) (plane_2_0_6_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_15 plane_3_1_7 plane_3_1_9 263577935163 47868557605 253947212243
      (by decide) p (plane_1_10_15_sound p h1) (plane_3_1_7_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_19 plane_2_0_9 plane_3_2_7 16091708513 27631156413 19219160425
      (by decide) p (plane_1_10_19_sound p h1) (plane_2_0_9_sound p h2) (plane_3_2_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_19 plane_2_0_9 plane_3_3_11 265998687433 194526752133 153753283400
      (by decide) p (plane_1_10_19_sound p h1) (plane_2_0_9_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_3_4_4 plane_3_4_10 284726497290 22752306341 282753367353
      (by decide) p (plane_2_0_6_sound p h2) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_2_0_8 plane_3_5_6 141060621963 181086258647 282797744028
      (by decide) p (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_8 plane_2_0_9 plane_3_6_6 148185826108 179026671 143061215619
      (by decide) p (plane_2_0_8_sound p h2) (plane_2_0_9_sound p h2) (plane_3_6_6_sound p h3))
  · refine ⟨(110 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row110]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_0_8 plane_3_8_4 378632391 568581733094 286092288567
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_0_8_sound p h2) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_0_8 plane_3_9_9 8920842114 576406739029 568648995369
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_0_8_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_0_8 plane_3_10_10 8920842114 576406739029 568648995369
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_0_8_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_0_8 plane_3_11_11 4445101833 282458329541 286092288567
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_0_8_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_0_8 plane_3_12_7 788225060550 1701134823476 568648995369
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_0_8_sound p h2) (plane_3_12_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_0_8 plane_3_13_13 358053342 589503107161 568648995369
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_0_8_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_0_8 plane_3_14_14 4222434513 568649365826 568648995369
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_0_8_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_0_8 plane_3_15_15 193641402 27081514433 27078523589
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_0_8_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_8_10_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 5 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_3_0_6 plane_3_0_8 282797744028 145011768897 3615241625
      (by decide) p (plane_1_10_10_sound p h1) (plane_3_0_6_sound p h3) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_15 plane_3_1_7 plane_3_1_9 263577935163 47868557605 253947212243
      (by decide) p (plane_1_10_15_sound p h1) (plane_3_1_7_sound p h3) (plane_3_1_9_sound p h3))
  · refine ⟨(111 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row111]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(112 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row112]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_10 plane_3_4_5 130559037301 53973194410 93067799921
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_10_sound p h1) (plane_3_4_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_15 plane_3_5_6 57059353488 35380788337 29287552159
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_15_sound p h1) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_3_6_6 plane_3_6_11 284027168089 235449636515 90948203851
      (by decide) p (plane_0_8_13_sound p h0) (plane_3_6_6_sound p h3) (plane_3_6_11_sound p h3))
  · refine ⟨(113 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row113]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_0_8_13 plane_3_8_13 235449636515 175377310627 544837118028
      (by decide) p (plane_0_8_4_sound p h0) (plane_0_8_13_sound p h0) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_3_9_9 289994215265 80715855727 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_3_10_10 289994215265 80715855727 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_3_11_11 282458329541 91202004916 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_0_8_13 plane_3_12_7 122944616755 425283705869 136209279507
      (by decide) p (plane_0_8_4_sound p h0) (plane_0_8_13_sound p h0) (plane_3_12_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_6 plane_3_13_13 plane_3_13_14 292231582690 184381206724 586487235117
      (by decide) p (plane_0_8_6_sound p h0) (plane_3_13_13_sound p h3) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_3_14_14 286091972249 84016202474 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_3_15_15 286123403553 84175305711 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_8_11_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    (e1 : labels 1 = 11)
    (e2 : labels 2 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 11 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 0 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_8_0 plane_2_0_6 plane_3_0_6 93400000000 1 1
      (by decide) p (plane_0_8_0_sound p h0) (plane_2_0_6_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_0_5 plane_3_1_6 8987118323 97786266987 91481833329
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_0_5_sound p h2) (plane_3_1_6_sound p h3))
  · refine ⟨(114 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row114]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_0_5 plane_3_3_6 39890497256 13408722488 30493944443
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_0_5_sound p h2) (plane_3_3_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_3_4_4 plane_3_4_10 284726497290 22752306341 282753367353
      (by decide) p (plane_2_0_6_sound p h2) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_2_0_8 plane_3_5_6 141060621963 181086258647 282797744028
      (by decide) p (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_0_9 plane_3_6_6 148185826108 148309456911 97305227619
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_0_9_sound p h2) (plane_3_6_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_0_9 plane_3_7_7 265998687433 248783313891 194610455238
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_0_9_sound p h2) (plane_3_7_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_0_8 plane_3_8_4 126210797 189549665123 95375342880
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_0_8_sound p h2) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_0_8 plane_3_9_9 8920842114 576406739029 568648995369
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_0_8_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_0_8 plane_3_10_10 8920842114 576406739029 568648995369
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_0_8_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_0_8 plane_3_11_11 1481700611 94164690509 95375342880
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_0_8_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_0_8 plane_3_12_12 8438500783 82927771297 95375342880
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_0_8_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_0_8 plane_3_13_13 358053342 589503107161 568648995369
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_0_8_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_0_8 plane_3_14_14 4222434513 568649365826 568648995369
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_0_8_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_0_8 plane_3_15_15 193641402 27081514433 27078523589
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_0_8_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_8_11_1 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    (e1 : labels 1 = 11)
    (e2 : labels 2 = 1)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 11 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 1 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_2_1_9 plane_3_0_6 565438832685 6587121193 282458329541
      (by decide) p (plane_0_8_8_sound p h0) (plane_2_1_9_sound p h2) (plane_3_0_6_sound p h3))
  · refine ⟨(115 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row115]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(116 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row116]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(117 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row117]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_1_9 plane_3_4_4 4222434513 568711803093 568581733094
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_4_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_2_1_9 plane_3_5_6 282190942442 190329353976 282458329541
      (by decide) p (plane_0_8_8_sound p h0) (plane_2_1_9_sound p h2) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_1_9 plane_3_6_6 520176509 589503107161 568581733094
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_6_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_1_9 plane_3_7_7 25176504088 248783313891 286092288567
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_1_9_sound p h2) (plane_3_7_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_1_9 plane_3_8_4 67699997 568648995369 286092288567
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_1_9_sound p h2) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_1_9 plane_3_9_9 9078349777 576406739029 568581733094
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_1_9 plane_3_10_10 9078349777 576406739029 568581733094
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_1_9 plane_3_11_11 4290134510 282494071527 286092288567
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_1_9_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_1_9 plane_3_12_12 25176504088 248783313891 286092288567
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_1_9_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_1_9 plane_3_13_13 520176509 589503107161 568581733094
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_1_9 plane_3_14_14 2189181980 284324682913 284290866547
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_2_1_9 plane_3_15_15 4222434513 568711803093 568581733094
      (by decide) p (plane_0_8_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_8_11_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    (e1 : labels 1 = 11)
    (e2 : labels 2 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 11 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 5 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_3_0_6 plane_3_0_8 565595488056 282585774453 6587121193
      (by decide) p (plane_0_8_8_sound p h0) (plane_3_0_6_sound p h3) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_2_5_5 plane_3_1_6 277812578482 92227723283 282458329541
      (by decide) p (plane_0_8_8_sound p h0) (plane_2_5_5_sound p h2) (plane_3_1_6_sound p h3))
  · refine ⟨(118 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row118]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_5_5 plane_3_3_6 248405159872 40226167464 286092288567
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_5_5_sound p h2) (plane_3_3_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_1_11_13 plane_3_4_9 565149005286 98843541670 562547462351
      (by decide) p (plane_0_8_8_sound p h0) (plane_1_11_13_sound p h1) (plane_3_4_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_0_8_13 plane_3_5_6 70761576674 63443117992 90658323513
      (by decide) p (plane_0_8_8_sound p h0) (plane_0_8_13_sound p h0) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_11_19 plane_3_6_6 296618913822 90948203851 274086016275
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_11_19_sound p h1) (plane_3_6_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_14 plane_3_7_7 plane_3_7_10 35158011431 43178365888 7750937394
      (by decide) p (plane_1_11_14_sound p h1) (plane_3_7_7_sound p h3) (plane_3_7_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_1_11_13 plane_3_8_13 539094743595 91202004916 562547462351
      (by decide) p (plane_0_8_8_sound p h0) (plane_1_11_13_sound p h1) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_11_19 plane_3_9_9 290023537794 80715855727 274086016275
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_11_19_sound p h1) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_10 plane_1_11_19 plane_3_10_10 48337256299 32057011318 46887091617
      (by decide) p (plane_1_11_10_sound p h1) (plane_1_11_19_sound p h1) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_11_19 plane_3_11_11 282494071527 91202004916 274086016275
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_11_19_sound p h1) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_13 plane_1_11_19 plane_3_12_12 248783313891 68452719217 569452994580
      (by decide) p (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_13 plane_1_11_19 plane_3_13_13 148309456911 10415553607 284726497290
      (by decide) p (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_13 plane_1_11_19 plane_3_14_14 286123403553 12377849851 569452994580
      (by decide) p (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_13 plane_1_11_19 plane_3_15_15 47692487307 2115090599 94908832430
      (by decide) p (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_8_15_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    (e1 : labels 1 = 15)
    (e2 : labels 2 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 15 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 0 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_8_0 plane_1_15_15 plane_3_0_6 8906214456000000 1057261 534921
      (by decide) p (plane_0_8_0_sound p h0) (plane_1_15_15_sound p h1) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_0 plane_1_15_15 plane_3_1_7 230240398092000000 984719 534921
      (by decide) p (plane_0_8_0_sound p h0) (plane_1_15_15_sound p h1) (plane_3_1_7_sound p h3))
  · refine ⟨(119 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row119]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(120 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row120]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_3_4_4 plane_3_4_10 94908832430 2115090599 47692487307
      (by decide) p (plane_1_15_15_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_5_6 47020207321 31389522761 47687671440
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_6_6 59675557 49436485637 47687671440
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_6_6_sound p h3))
  · refine ⟨(121 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row121]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_8_6 37675206821 37761496117 19075068576
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_9_9 1486807019 48337256299 47687671440
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_10_10 1486807019 48337256299 47687671440
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_16 plane_2_0_8 plane_3_11_11 1481700611 81744026827 82927771297
      (by decide) p (plane_0_8_16_sound p h0) (plane_2_0_8_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_12_7 26274168685 28514397437 9537534288
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_12_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_13_13 59675557 49436485637 47687671440
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_14_14 1407478171 95374467851 95375342880
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_15_15 225914969 15897495769 15895890480
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_8_15_1 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    (e1 : labels 1 = 15)
    (e2 : labels 2 = 1)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 15 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 1 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_8_0 plane_1_15_15 plane_3_0_6 8906214456000000 1057261 534921
      (by decide) p (plane_0_8_0_sound p h0) (plane_1_15_15_sound p h1) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_0 plane_1_15_15 plane_3_1_7 230240398092000000 984719 534921
      (by decide) p (plane_0_8_0_sound p h0) (plane_1_15_15_sound p h1) (plane_3_1_7_sound p h3))
  · refine ⟨(122 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row122]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(123 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row123]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_3_4_4 plane_3_4_10 94908832430 2115090599 47692487307
      (by decide) p (plane_1_15_15_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_1_9 plane_3_5_6 282190942442 188337136566 286092288567
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_1_9_sound p h2) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_1_9 plane_3_6_6 520176509 296618913822 286092288567
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_1_9_sound p h2) (plane_3_6_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_16 plane_2_1_9 plane_3_7_7 25176504088 214074416447 248740136971
      (by decide) p (plane_0_8_16_sound p h0) (plane_2_1_9_sound p h2) (plane_3_7_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_1_9 plane_3_8_4 plane_3_8_6 1123889340121 565371132688 67699997
      (by decide) p (plane_2_1_9_sound p h2) (plane_3_8_4_sound p h3) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_1_9 plane_3_9_9 9078349777 290023537794 286092288567
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_1_9_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_1_9 plane_3_10_10 9078349777 290023537794 286092288567
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_1_9_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_16 plane_2_1_9 plane_3_11_11 4290134510 245232080481 248740136971
      (by decide) p (plane_0_8_16_sound p h0) (plane_2_1_9_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_1_9 plane_3_12_7 788599788472 855431923110 286092288567
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_1_9_sound p h2) (plane_3_12_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_1_9 plane_3_13_13 520176509 296618913822 286092288567
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_1_9_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_1_9 plane_3_14_14 4378363960 286123403553 286092288567
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_1_9_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_1_9 plane_3_15_15 1407478171 95384974614 95364096189
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_1_9_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_8_15_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    (e1 : labels 1 = 15)
    (e2 : labels 2 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 15 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 5 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_5_5 plane_3_0_6 3695678645 14552638 1869884239
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_5_5_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_5_5 plane_3_1_6 277812578482 97786266987 286092288567
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_5_5_sound p h2) (plane_3_1_6_sound p h3))
  · refine ⟨(124 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row124]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(125 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row125]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_3_4_4 plane_3_4_10 94908832430 2115090599 47692487307
      (by decide) p (plane_1_15_15_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_1_15_17 plane_3_5_6 275461549151 94168568283 282797744028
      (by decide) p (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_16 plane_1_15_14 plane_3_6_6 201389209616 257938437109 265998687433
      (by decide) p (plane_0_8_16_sound p h0) (plane_1_15_14_sound p h1) (plane_3_6_6_sound p h3))
  · refine ⟨(126 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row126]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_1_15_17 plane_3_8_6 365596738813 188807480585 188531829352
      (by decide) p (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_3_9_9 plane_3_9_15 288682233706 6345271797 145011768897
      (by decide) p (plane_1_15_15_sound p h1) (plane_3_9_9_sound p h3) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_1_15_17 plane_3_10_10 3615241625 145011768897 282797744028
      (by decide) p (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_16 plane_1_15_17 plane_3_11_11 18920357693 245232080481 492686929159
      (by decide) p (plane_0_8_16_sound p h0) (plane_1_15_17_sound p h1) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_1_15_17 plane_3_12_7 254571102501 142571987185 94265914676
      (by decide) p (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1) (plane_3_12_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_17 plane_3_13_13 plane_3_13_14 146115791345 275461549151 4966236753
      (by decide) p (plane_1_15_17_sound p h1) (plane_3_13_13_sound p h3) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_16 plane_1_15_17 plane_3_14_14 1917121227 249154618709 492686929159
      (by decide) p (plane_0_8_16_sound p h0) (plane_1_15_17_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_8_16 plane_1_15_17 plane_3_15_15 2226553614 249168225957 492686929159
      (by decide) p (plane_0_8_16_sound p h0) (plane_1_15_17_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_8_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    (e1 : labels 1 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact complete_8_10_0 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_8_16 plane_1_10_15 plane_2_1_9 91348355030 248740136971 240683185084
      (by decide) p (plane_0_8_16_sound p h0) (plane_1_10_15_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_15 plane_2_2_5 155927910211 118124305790 87862656477
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_15_sound p h1) (plane_2_2_5_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_10 plane_2_3_5 74753504753 484979591212 279203399763
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_10_sound p h1) (plane_2_3_5_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_0_8_16 plane_2_4_9 7750937394 43178365888 35158011431
      (by decide) p (plane_0_8_13_sound p h0) (plane_0_8_16_sound p h0) (plane_2_4_9_sound p h2))
  · exact complete_8_10_5 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_2_6_6 plane_2_6_8 590105431712 539094743595 87603658687
      (by decide) p (plane_0_8_13_sound p h0) (plane_2_6_6_sound p h2) (plane_2_6_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_0_8_13 plane_2_7_6 33280578321 70437934891 90806186338
      (by decide) p (plane_0_8_4_sound p h0) (plane_0_8_13_sound p h0) (plane_2_7_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_2_8_4 568649365826 166929547819 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_2_8_4_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_2_9_9 289889229815 93829213027 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_2_9_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_2_10_10 289889229815 93829213027 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_2_11_11 282557077259 78867780424 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_2_11_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_2_12_12 249154618709 49047509706 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_2_13_13 296610908583 87603658687 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_10_18 plane_2_14_14 286058466951 88201229486 274101840469
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_10_18_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_6 plane_2_15_15 plane_2_15_17 188531829352 365596738813 188807480585
      (by decide) p (plane_0_8_6_sound p h0) (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2))

theorem complete_8_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    (e1 : labels 1 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 11 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact complete_8_11_0 labels p h e0 e1 he
  · exact complete_8_11_1 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_2_2_5 plane_2_2_9 279339316598 177664844544 104793484997
      (by decide) p (plane_0_8_8_sound p h0) (plane_2_2_5_sound p h2) (plane_2_2_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_1_11_13 plane_2_3_5 1044483374653 72410295677 562547462351
      (by decide) p (plane_0_8_8_sound p h0) (plane_1_11_13_sound p h1) (plane_2_3_5_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_11_19 plane_2_4_9 91515573402 302248561216 274086016275
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_11_19_sound p h1) (plane_2_4_9_sound p h2))
  · exact complete_8_11_5 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_2_6_6 plane_2_6_8 590105431712 539094743595 87603658687
      (by decide) p (plane_0_8_13_sound p h0) (plane_2_6_6_sound p h2) (plane_2_6_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_1_11_10 plane_2_7_6 41580172695 140875869782 186455027823
      (by decide) p (plane_0_8_4_sound p h0) (plane_1_11_10_sound p h1) (plane_2_7_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_11_19 plane_2_8_8 282585774453 78867780424 274086016275
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_11_19_sound p h1) (plane_2_8_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_10 plane_1_11_19 plane_2_9_9 48321007024 34294140193 46887091617
      (by decide) p (plane_1_11_10_sound p h1) (plane_1_11_19_sound p h1) (plane_2_9_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_10 plane_1_11_19 plane_2_10_10 48321007024 34294140193 46887091617
      (by decide) p (plane_1_11_10_sound p h1) (plane_1_11_19_sound p h1) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_10 plane_2_11_11 plane_2_11_13 561792632189 545482288026 187637155215
      (by decide) p (plane_1_11_10_sound p h1) (plane_2_11_11_sound p h2) (plane_2_11_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_1_11_13 plane_2_12_12 39328026361 495236966130 1131762613157
      (by decide) p (plane_0_8_4_sound p h0) (plane_1_11_13_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_13 plane_1_11_19 plane_2_13_13 74160944991 3467060182 142363248645
      (by decide) p (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_13 plane_1_11_19 plane_2_14_14 286092288567 21090479789 569452994580
      (by decide) p (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_13 plane_1_11_19 plane_2_15_15 4768767144 346360051 9490883243
      (by decide) p (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_8_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    (e1 : labels 1 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 15 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact complete_8_15_0 labels p h e0 e1 he
  · exact complete_8_15_1 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_2_4 plane_2_2_10 146561981297 74160944991 2565962934
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_13 plane_1_15_15 plane_2_3_5 65045933361 979437441292 569452994580
      (by decide) p (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1) (plane_2_3_5_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_16 plane_1_15_14 plane_2_4_4 194610455238 248783313891 265998687433
      (by decide) p (plane_0_8_16_sound p h0) (plane_1_15_14_sound p h1) (plane_2_4_4_sound p h2))
  · exact complete_8_15_5 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_15_13 plane_1_15_15 plane_2_6_8 1039080153 55552212773 28472649729
      (by decide) p (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1) (plane_2_6_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_7_6 plane_2_7_19 77676143209 81244543299 30352639179
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_7_6_sound p h2) (plane_2_7_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_1_15_17 plane_2_8_8 6587121193 282585774453 565595488056
      (by decide) p (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1) (plane_2_8_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_0_8_16 plane_2_9_9 251662704291 93829213027 246106080017
      (by decide) p (plane_0_8_13_sound p h0) (plane_0_8_16_sound p h0) (plane_2_9_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_17 plane_2_10_10 plane_2_10_12 112810242211 219687422719 3977652280
      (by decide) p (plane_1_15_17_sound p h1) (plane_2_10_10_sound p h2) (plane_2_10_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_11_13 plane_2_11_19 9490883243 4768767144 346360051
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_1_15_17 plane_2_12_12 48098237513 249168225957 565595488056
      (by decide) p (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_8_16 plane_1_15_17 plane_2_13_13 3015872044 258269678195 492686929159
      (by decide) p (plane_0_8_16_sound p h0) (plane_1_15_17_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_17 plane_2_14_14 plane_2_14_16 527155870326 1039767016309 10571859773
      (by decide) p (plane_1_15_17_sound p h1) (plane_2_14_14_sound p h2) (plane_2_14_16_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_17 plane_2_15_13 plane_2_15_15 142363248645 2565962934 278662161113
      (by decide) p (plane_1_15_17_sound p h1) (plane_2_15_13_sound p h2) (plane_2_15_15_sound p h2))

theorem complete_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 8 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_0_8_6 plane_1_0_8 565128102315 378632391 1123889340121
      (by decide) p (plane_0_8_4_sound p h0) (plane_0_8_6_sound p h0) (plane_1_0_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_0_8_6 plane_1_1_9 565371132688 67699997 1123889340121
      (by decide) p (plane_0_8_4_sound p h0) (plane_0_8_6_sound p h0) (plane_1_1_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_8_4 plane_1_2_4 plane_1_2_10 586247925188 8058987727 1124082257821
      (by decide) p (plane_0_8_4_sound p h0) (plane_1_2_4_sound p h1) (plane_1_2_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_0_8_13 plane_1_3_11 229802962879 32358495242 271974970539
      (by decide) p (plane_0_8_8_sound p h0) (plane_0_8_13_sound p h0) (plane_1_3_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_4_10 plane_1_4_12 561792632189 268090853421 155354934215
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_4_10_sound p h1) (plane_1_4_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_5_11 plane_1_5_13 564051211055 279203399763 144242387873
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_5_11_sound p h1) (plane_1_5_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_0_8_13 plane_1_6_15 11497565201 31203773929 30219441171
      (by decide) p (plane_0_8_8_sound p h0) (plane_0_8_13_sound p h0) (plane_1_6_15_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_8_8 plane_0_8_13 plane_1_7_15 89363617807 4247703980 90658323513
      (by decide) p (plane_0_8_8_sound p h0) (plane_0_8_13_sound p h0) (plane_1_7_15_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_0_8_16 plane_1_8_14 486091341318 144242387873 246106080017
      (by decide) p (plane_0_8_13_sound p h0) (plane_0_8_16_sound p h0) (plane_1_8_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_1_9_15 plane_1_9_17 590105431712 282973951883 155354934215
      (by decide) p (plane_0_8_13_sound p h0) (plane_1_9_15_sound p h1) (plane_1_9_17_sound p h1))
  · exact complete_8_10 labels p h e0 he
  · exact complete_8_11 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_0_8_16 plane_1_12_18 464134193302 99943510283 246106080017
      (by decide) p (plane_0_8_13_sound p h0) (plane_0_8_16_sound p h0) (plane_1_12_18_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_8_13 plane_0_8_16 plane_1_13_19 492686929159 164242869823 246106080017
      (by decide) p (plane_0_8_13_sound p h0) (plane_0_8_16_sound p h0) (plane_1_13_19_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_8_16 plane_1_14_14 plane_1_14_19 286195087637 240822183345 25176504088
      (by decide) p (plane_0_8_16_sound p h0) (plane_1_14_14_sound p h1) (plane_1_14_19_sound p h1))
  · exact complete_8_15 labels p h e0 he

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_8
