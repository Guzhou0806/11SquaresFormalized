import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 0.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_0_2_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 0)
    (e1 : labels 1 = 2)
    (e2 : labels 2 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 0 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 7 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(0 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row0]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_7_7 plane_3_1_8 plane_3_1_9 71509664711 6294126022 53876670249
      (by decide) p (plane_2_7_7_sound p h2) (plane_3_1_8_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_3_2_4 plane_3_2_10 146561981297 74160944991 2565962934
      (by decide) p (plane_0_0_8_sound p h0) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_3_5 1047812442533 65045933361 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(1 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row1]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_0_9 plane_1_2_11 plane_3_5_4 415576003437 153753283400 394732355537
      (by decide) p (plane_0_0_9_sound p h0) (plane_1_2_11_sound p h1) (plane_3_5_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_6_8 1131762613157 20781603060 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_7_9 85032210779 2163220827 43742230413
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_8_8 282585774453 6587121193 565595488056
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_9_9 plane_3_9_12 275073929313 542395821437 19888261400
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_9_9_sound p h3) (plane_3_9_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_10_10 plane_3_10_17 140046111449 279528582101 9944130700
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_11_13 1131762613157 20781603060 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_12_12 249168225957 48098237513 565595488056
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_13_13 plane_3_13_16 64367991506 122820427970 753968011
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_13_13_sound p h3) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_14_14 plane_3_14_16 527155870326 1039767016309 10571859773
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_14_14_sound p h3) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_15_17 1124082257821 10263851736 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_0_3_3 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 0)
    (e1 : labels 1 = 3)
    (e2 : labels 2 = 3)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 0 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 3 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 3 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(2 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row2]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_0_0 plane_1_3_11 plane_3_1_4 108426769676000000 268211 232722
      (by decide) p (plane_0_0_0_sound p h0) (plane_1_3_11_sound p h1) (plane_3_1_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_3_2_4 plane_3_2_10 146561981297 74160944991 2565962934
      (by decide) p (plane_0_0_8_sound p h0) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_3_5 65045933361 1039767016309 565595488056
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_3_11 plane_3_4_4 8438500783 95375342880 82927771297
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_3_11_sound p h2) (plane_3_4_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_3_11 plane_2_3_11 plane_3_5_4 265998687433 194526752133 214074416447
      (by decide) p (plane_1_3_11_sound p h1) (plane_2_3_11_sound p h2) (plane_3_5_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_6_8 5195400765 281228124047 141398872014
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_3_7_9 plane_3_7_19 1104672086663 568711803093 28121870751
      (by decide) p (plane_0_0_8_sound p h0) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_3_11 plane_3_8_8 32358495242 282585774453 248783313891
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_3_11_sound p h2) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_3_11 plane_3_9_9 21478273037 289926042144 248783313891
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_3_11_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_10_10 plane_3_10_17 140046111449 279528582101 9944130700
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_3_11_13 plane_3_11_19 9490883243 4768767144 346360051
      (by decide) p (plane_0_0_8_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_12_12 249168225957 48098237513 565595488056
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_13_13 plane_3_13_16 64367991506 122820427970 753968011
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_13_13_sound p h3) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_14_14 plane_3_14_16 527155870326 1039767016309 10571859773
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_14_14_sound p h3) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_15_17 427660489 46569354854 23566478669
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_15_17_sound p h3))

theorem complete_0_3_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 0)
    (e1 : labels 1 = 3)
    (e2 : labels 2 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 0 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 3 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 7 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(3 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row3]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_7_7 plane_3_1_8 plane_3_1_9 71509664711 6294126022 53876670249
      (by decide) p (plane_2_7_7_sound p h2) (plane_3_1_8_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_3_2_4 plane_3_2_10 146561981297 74160944991 2565962934
      (by decide) p (plane_0_0_8_sound p h0) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_3_5 1047812442533 65045933361 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_5 plane_1_3_6 plane_3_4_4 13408722488 30493944443 39890497256
      (by decide) p (plane_0_0_5_sound p h0) (plane_1_3_6_sound p h1) (plane_3_4_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_9 plane_1_3_11 plane_3_5_4 194526752133 153753283400 265998687433
      (by decide) p (plane_0_0_9_sound p h0) (plane_1_3_11_sound p h1) (plane_3_5_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_6_8 1131762613157 20781603060 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_7_9 85032210779 2163220827 43742230413
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_8_8 282585774453 6587121193 565595488056
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_9_9 plane_3_9_12 275073929313 542395821437 19888261400
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_9_9_sound p h3) (plane_3_9_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_10_10 plane_3_10_17 140046111449 279528582101 9944130700
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_11_13 1131762613157 20781603060 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_12_12 249168225957 48098237513 565595488056
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_13_13 plane_3_13_16 64367991506 122820427970 753968011
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_13_13_sound p h3) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_14_14 plane_3_14_16 527155870326 1039767016309 10571859773
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_14_14_sound p h3) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_15_17 1124082257821 10263851736 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_0_7_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 0)
    (e1 : labels 1 = 7)
    (e2 : labels 2 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 0 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 2 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(4 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row4]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(5 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row5]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_2_10 plane_3_2_4 97720717173 1710641956 49436485637
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_2_10_sound p h2) (plane_3_2_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_2_10 plane_3_3_5 546434044369 65045933361 296618913822
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_2_10_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_2_11 plane_3_4_4 plane_3_4_9 286122431238 121004392604 273727962933
      (by decide) p (plane_2_2_11_sound p h2) (plane_3_4_4_sound p h3) (plane_3_4_9_sound p h3))
  · refine ⟨(6 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row6]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_2_10 plane_3_6_8 295155055633 10390801530 148309456911
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_2_10_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_2_10 plane_3_7_9 576554357591 28121870751 296618913822
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_2_10_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_2_10 plane_3_8_4 1151283961 81244543299 42374130546
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_2_10_sound p h2) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_2_10 plane_3_9_9 plane_3_9_12 275073929313 282973951883 5338712606
      (by decide) p (plane_2_2_10_sound p h2) (plane_3_9_9_sound p h3) (plane_3_9_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_2_10 plane_3_10_10 plane_3_10_17 140046111449 144976325411 2669356303
      (by decide) p (plane_2_2_10_sound p h2) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_2_10 plane_3_11_13 295155055633 10390801530 148309456911
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_2_10_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_2_10 plane_3_12_12 4228590959 35595460851 42374130546
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_2_10_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_2_10 plane_3_13_13 259125349 21188841426 21187065273
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_2_10_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_2_10 plane_3_14_14 plane_3_14_16 527155870326 546434044369 520176509
      (by decide) p (plane_2_2_10_sound p h2) (plane_3_14_14_sound p h3) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_2_10 plane_3_15_15 plane_3_15_17 94265914676 97720717173 59675557
      (by decide) p (plane_2_2_10_sound p h2) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_0_7_3 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 0)
    (e1 : labels 1 = 7)
    (e2 : labels 2 = 3)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 0 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 3 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(7 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row7]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(8 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row8]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_3_2_4 plane_3_2_10 146561981297 74160944991 2565962934
      (by decide) p (plane_0_0_8_sound p h0) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_3_5 65045933361 1039767016309 565595488056
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_3_11 plane_3_4_4 8438500783 95375342880 82927771297
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_3_11_sound p h2) (plane_3_4_4_sound p h3))
  · refine ⟨(9 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row9]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_6_8 5195400765 281228124047 141398872014
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_3_7_9 plane_3_7_19 1104672086663 568711803093 28121870751
      (by decide) p (plane_0_0_8_sound p h0) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_7_6 plane_3_8_4 140875869782 189570601031 91242654311
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_7_6_sound p h1) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_7_6 plane_3_9_9 68911691945 96642014048 91242654311
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_7_6_sound p h1) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_10_10 plane_3_10_17 140046111449 279528582101 9944130700
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_3_11_13 plane_3_11_19 9490883243 4768767144 346360051
      (by decide) p (plane_0_0_8_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_12_12 249168225957 48098237513 565595488056
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_1_7_7 plane_3_13_13 258269678195 3015872044 492686929159
      (by decide) p (plane_0_0_6_sound p h0) (plane_1_7_7_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_14_14 plane_3_14_16 527155870326 1039767016309 10571859773
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_14_14_sound p h3) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_15_17 427660489 46569354854 23566478669
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_15_17_sound p h3))

theorem complete_0_7_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 0)
    (e1 : labels 1 = 7)
    (e2 : labels 2 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 0 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 7 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(10 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row10]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_7_7 plane_2_7_7 plane_3_1_9 25176504088 248740136971 214074416447
      (by decide) p (plane_1_7_7_sound p h1) (plane_2_7_7_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_3_2_4 plane_3_2_10 146561981297 74160944991 2565962934
      (by decide) p (plane_0_0_8_sound p h0) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_3_5 1047812442533 65045933361 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_3_4_4 plane_3_4_9 13624877678 9858040810 9931292687
      (by decide) p (plane_1_7_6_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_9_sound p h3))
  · refine ⟨(11 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row11]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_6_8 1131762613157 20781603060 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_7_9 85032210779 2163220827 43742230413
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_7_6 plane_3_8_4 140875869782 189570601031 91242654311
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_7_6_sound p h1) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_7_6 plane_3_9_9 68911691945 96642014048 91242654311
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_7_6_sound p h1) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_10_10 plane_3_10_17 140046111449 279528582101 9944130700
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_11_13 1131762613157 20781603060 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_3_12_12 249168225957 48098237513 565595488056
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_1_7_7 plane_3_13_13 258269678195 3015872044 492686929159
      (by decide) p (plane_0_0_6_sound p h0) (plane_1_7_7_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_3_14_14 plane_3_14_16 527155870326 1039767016309 10571859773
      (by decide) p (plane_0_0_6_sound p h0) (plane_3_14_14_sound p h3) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_7_19 plane_3_15_17 1124082257821 10263851736 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_7_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_0_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 0)
    (e1 : labels 1 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 0 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_2_11 plane_2_0_6 539379949393 2226553614 273727962933
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_2_11_sound p h1) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_2_11 plane_2_1_7 461550255767 57560099523 273727962933
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_2_11_sound p h1) (plane_2_1_7_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_9 plane_1_2_11 plane_2_2_11 109849895569 415576003437 394732355537
      (by decide) p (plane_0_0_9_sound p h0) (plane_1_2_11_sound p h1) (plane_2_2_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_7 plane_1_2_11 plane_2_3_11 157119495031 56954921416 219550877952
      (by decide) p (plane_1_2_7_sound p h1) (plane_1_2_11_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_4_4 plane_2_4_10 94908832430 2115090599 47692487307
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_5_5 plane_2_5_11 556142498998 20220009861 286123403553
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_5_5_sound p h2) (plane_2_5_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_9 plane_2_6_6 plane_2_6_11 40575309727 30598113403 28769887088
      (by decide) p (plane_0_0_9_sound p h0) (plane_2_6_6_sound p h2) (plane_2_6_11_sound p h2))
  · exact complete_0_2_7 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_8_4 plane_2_8_14 1104672086663 20220009861 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_9_9 plane_2_9_15 288682233706 6345271797 145011768897
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_2_10_10 145011768897 3615241625 282797744028
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_2 plane_0_0_6 plane_2_11_11 75681430772000000 528190 1057261
      (by decide) p (plane_0_0_2_sound p h0) (plane_0_0_6_sound p h0) (plane_2_11_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_2_12_12 plane_2_12_18 452528907170 1042442973009 58966354913
      (by decide) p (plane_0_0_6_sound p h0) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_2_13_13 plane_2_13_19 293123962594 558968563873 4966236753
      (by decide) p (plane_0_0_6_sound p h0) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_2_14_14 plane_2_14_19 286195087637 565096908217 1917121227
      (by decide) p (plane_0_0_6_sound p h0) (plane_2_14_14_sound p h2) (plane_2_14_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_2 plane_0_0_6 plane_2_15_15 8906214456000000 534921 1057261
      (by decide) p (plane_0_0_2_sound p h0) (plane_0_0_6_sound p h0) (plane_2_15_15_sound p h2))

theorem complete_0_3 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 0)
    (e1 : labels 1 = 3)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 0 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 3 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_0_0 plane_0_0_8 plane_2_0_6 8906214456000000 1057261 534921
      (by decide) p (plane_0_0_0_sound p h0) (plane_0_0_8_sound p h0) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_0 plane_0_0_8 plane_2_1_7 230240398092000000 984719 534921
      (by decide) p (plane_0_0_0_sound p h0) (plane_0_0_8_sound p h0) (plane_2_1_7_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_3_11 plane_2_2_7 plane_2_2_11 219550877952 157119495031 56954921416
      (by decide) p (plane_1_3_11_sound p h1) (plane_2_2_7_sound p h2) (plane_2_2_11_sound p h2))
  · exact complete_0_3_3 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_4_4 plane_2_4_10 94908832430 2115090599 47692487307
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_5_5 plane_2_5_11 556142498998 20220009861 286123403553
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_5_5_sound p h2) (plane_2_5_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_9 plane_2_6_6 plane_2_6_11 40575309727 30598113403 28769887088
      (by decide) p (plane_0_0_9_sound p h0) (plane_2_6_6_sound p h2) (plane_2_6_11_sound p h2))
  · exact complete_0_3_7 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_8_4 plane_2_8_14 1104672086663 20220009861 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_9_9 plane_2_9_15 288682233706 6345271797 145011768897
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_2_10_10 145011768897 3615241625 282797744028
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_2 plane_0_0_6 plane_2_11_11 75681430772000000 528190 1057261
      (by decide) p (plane_0_0_2_sound p h0) (plane_0_0_6_sound p h0) (plane_2_11_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_2_12_12 plane_2_12_18 452528907170 1042442973009 58966354913
      (by decide) p (plane_0_0_6_sound p h0) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_2_13_13 plane_2_13_19 293123962594 558968563873 4966236753
      (by decide) p (plane_0_0_6_sound p h0) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_2_14_14 plane_2_14_19 286195087637 565096908217 1917121227
      (by decide) p (plane_0_0_6_sound p h0) (plane_2_14_14_sound p h2) (plane_2_14_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_2 plane_0_0_6 plane_2_15_15 8906214456000000 534921 1057261
      (by decide) p (plane_0_0_2_sound p h0) (plane_0_0_6_sound p h0) (plane_2_15_15_sound p h2))

theorem complete_0_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 0)
    (e1 : labels 1 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 0 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_0_0 plane_0_0_8 plane_2_0_6 8906214456000000 1057261 534921
      (by decide) p (plane_0_0_0_sound p h0) (plane_0_0_8_sound p h0) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_0 plane_0_0_8 plane_2_1_7 230240398092000000 984719 534921
      (by decide) p (plane_0_0_0_sound p h0) (plane_0_0_8_sound p h0) (plane_2_1_7_sound p h2))
  · exact complete_0_7_2 labels p h e0 e1 he
  · exact complete_0_7_3 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_4_4 plane_2_4_10 94908832430 2115090599 47692487307
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_5_5 plane_2_5_11 556142498998 20220009861 286123403553
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_5_5_sound p h2) (plane_2_5_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_7_6 plane_2_6_6 216547944797 296618913822 273727962933
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_7_6_sound p h1) (plane_2_6_6_sound p h2))
  · exact complete_0_7_7 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_8_4 plane_2_8_14 1104672086663 20220009861 568648995369
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_2_9_9 plane_2_9_15 288682233706 6345271797 145011768897
      (by decide) p (plane_0_0_8_sound p h0) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_7_6 plane_2_10_10 73310778095 96674512598 91242654311
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_7_6_sound p h1) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_7_6 plane_2_11_11 67219107427 94164690509 91242654311
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_7_6_sound p h1) (plane_2_11_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_2_12_12 plane_2_12_18 452528907170 1042442973009 58966354913
      (by decide) p (plane_0_0_6_sound p h0) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_7_6 plane_2_13_13 216547944797 296618913822 273727962933
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_7_6_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_1_7_7 plane_2_14_14 249154618709 1917121227 492686929159
      (by decide) p (plane_0_0_6_sound p h0) (plane_1_7_7_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_1_7_7 plane_2_15_15 249168225957 2226553614 492686929159
      (by decide) p (plane_0_0_6_sound p h0) (plane_1_7_7_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 0 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_0_2 plane_0_0_6 plane_1_0_6 93400000000 1 1
      (by decide) p (plane_0_0_2_sound p h0) (plane_0_0_6_sound p h0) (plane_1_0_6_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_0_5 plane_1_1_7 plane_1_1_9 527155870326 287626254203 110684373445
      (by decide) p (plane_0_0_5_sound p h0) (plane_1_1_7_sound p h1) (plane_1_1_9_sound p h1))
  · exact complete_0_2 labels p h e0 he
  · exact complete_0_3 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_1_4_4 plane_1_4_10 284726497290 22752306341 282753367353
      (by decide) p (plane_0_0_6_sound p h0) (plane_1_4_4_sound p h1) (plane_1_4_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_1_5_6 141060621963 181086258647 282797744028
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_1_5_6_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_1_6_6 59675557 97720717173 94265914676
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_1_6_6_sound p h1))
  · exact complete_0_7 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_8_4 plane_1_8_14 1104672086663 555849206859 378632391
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_8_4_sound p h1) (plane_1_8_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_1_9_9 4460421057 286489913177 282797744028
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_1_9_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_1_10_10 4460421057 286489913177 282797744028
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_1_10_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_0_0 plane_0_0_8 plane_1_11_11 17780407332000000 528190 534921
      (by decide) p (plane_0_0_0_sound p h0) (plane_0_0_8_sound p h0) (plane_1_11_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_12_12 plane_1_12_18 452528907170 526311269997 25315502349
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_12_12_sound p h1) (plane_1_12_18_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_1_13_13 59675557 97720717173 94265914676
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_1_13_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_0_6 plane_0_0_8 plane_1_14_14 1407478171 188479610895 188531829352
      (by decide) p (plane_0_0_6_sound p h0) (plane_0_0_8_sound p h0) (plane_1_14_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_0_8 plane_1_15_13 plane_1_15_15 94908832430 677744907 94191446894
      (by decide) p (plane_0_0_8_sound p h0) (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_0
