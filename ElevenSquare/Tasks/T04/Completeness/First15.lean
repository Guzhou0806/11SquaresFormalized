import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 15.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_15_8_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 15)
    (e1 : labels 1 = 8)
    (e2 : labels 2 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 15 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 8 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_0_6 1124082257821 10263851736 568648995369
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_1_9 67699997 286092288567 568648995369
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_2_10 1151283961 42377682852 81235570767
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_3_11 48098237513 249168225957 565595488056
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_4_10 1131762613157 20781603060 568648995369
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_5_11 plane_3_5_13 112810242211 3977652280 219687422719
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_5_11_sound p h3) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_1_8_16 plane_3_6_14 251662704291 19888261400 492686929159
      (by decide) p (plane_0_15_17_sound p h0) (plane_1_8_16_sound p h1) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_7_15 6587121193 282585774453 565595488056
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_8_13 plane_3_8_16 35158011431 35595460851 12025043673
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_9_15 281228124047 5195400765 141398872014
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_9_15_sound p h3))
  · refine ⟨(208 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row208]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_8_17 plane_3_11_14 plane_3_11_19 13624877678 9931292687 9858040810
      (by decide) p (plane_1_8_17_sound p h1) (plane_3_11_14_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_16 plane_3_12_14 146319229738 73682118402 82927771297
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_16_sound p h2) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_16 plane_3_13_14 75562747242 61448867834 82927771297
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_16_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_16 plane_2_8_16 plane_3_14_14 25176504088 248740136971 214074416447
      (by decide) p (plane_1_8_16_sound p h1) (plane_2_8_16_sound p h2) (plane_3_14_14_sound p h3))
  · refine ⟨(209 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row209]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_15_8_12 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 15)
    (e1 : labels 1 = 8)
    (e2 : labels 2 = 12)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 15 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 12 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_0_6 plane_3_0_8 23566478669 427660489 46569354854
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_0_6_sound p h3) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_1_7 plane_3_1_9 527155870326 10571859773 1039767016309
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_1_7_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_1_8_16 plane_3_2_10 258269678195 3015872044 492686929159
      (by decide) p (plane_0_15_17_sound p h0) (plane_1_8_16_sound p h1) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_3_11 48098237513 249168225957 565595488056
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_4_10 281228124047 5195400765 141398872014
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_5_11 plane_3_5_13 112810242211 3977652280 219687422719
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_5_11_sound p h3) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_1_8_16 plane_3_6_14 251662704291 19888261400 492686929159
      (by decide) p (plane_0_15_17_sound p h0) (plane_1_8_16_sound p h1) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_7_15 6587121193 282585774453 565595488056
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_8_13 plane_3_8_16 35158011431 35595460851 12025043673
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_9_15 281228124047 5195400765 141398872014
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_9_15_sound p h3))
  · refine ⟨(210 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row210]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_12_12 plane_3_11_19 8438500783 95375342880 82927771297
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_12_12_sound p h2) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_12_14 plane_3_12_18 175718623442 21681977787 73682118402
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_12_14_sound p h3) (plane_3_12_18_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_13_14 plane_3_13_19 187214839747 5131925868 92173301751
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_13_14_sound p h3) (plane_3_13_19_sound p h3))
  · refine ⟨(211 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row211]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(212 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row212]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_15_8_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 15)
    (e1 : labels 1 = 8)
    (e2 : labels 2 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 15 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 13 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_2_13_13 plane_3_0_6 plane_3_0_8 94265914676 59675557 97720717173
      (by decide) p (plane_2_13_13_sound p h2) (plane_3_0_6_sound p h3) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_13 plane_3_1_7 plane_3_1_9 527155870326 520176509 546434044369
      (by decide) p (plane_2_13_13_sound p h2) (plane_3_1_7_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_13_13 plane_3_2_10 259125349 21188841426 21187065273
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_13_13_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_13_13 plane_3_3_11 4228590959 35595460851 42374130546
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_13_13_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_13_13 plane_3_4_10 295155055633 10390801530 148309456911
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_13_13_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_13 plane_3_5_11 plane_3_5_13 29686905845 280984874 30344966189
      (by decide) p (plane_2_13_13_sound p h2) (plane_3_5_11_sound p h3) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_16 plane_2_13_13 plane_3_6_14 5338712606 251662704291 257938437109
      (by decide) p (plane_1_8_16_sound p h1) (plane_2_13_13_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_13_13 plane_3_7_15 8417041069 282585774453 296618913822
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_13_13_sound p h2) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_8_13 plane_3_8_16 35158011431 35595460851 12025043673
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_13_13 plane_3_9_15 295155055633 10390801530 148309456911
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_13_13_sound p h2) (plane_3_9_15_sound p h3))
  · refine ⟨(213 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row213]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_8_17 plane_3_11_14 plane_3_11_19 13624877678 9931292687 9858040810
      (by decide) p (plane_1_8_17_sound p h1) (plane_3_11_14_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_12_14 plane_3_12_18 175718623442 21681977787 73682118402
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_12_14_sound p h3) (plane_3_12_18_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_13_14 plane_3_13_19 187214839747 5131925868 92173301751
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_13_14_sound p h3) (plane_3_13_19_sound p h3))
  · refine ⟨(214 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row214]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(215 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row215]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_15_12_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 15)
    (e1 : labels 1 = 12)
    (e2 : labels 2 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 15 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 12 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 8 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_0_6 1124082257821 10263851736 568648995369
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_1_9 67699997 286092288567 568648995369
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_2_10 1151283961 42377682852 81235570767
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_3_11 48098237513 249168225957 565595488056
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_4_10 1131762613157 20781603060 568648995369
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_5_11 plane_3_5_13 112810242211 3977652280 219687422719
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_5_11_sound p h3) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_6_11 plane_3_6_14 275073929313 19888261400 542395821437
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_6_11_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_7_15 6587121193 282585774453 565595488056
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_8_13 plane_3_8_16 35158011431 35595460851 12025043673
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_9_15 281228124047 5195400765 141398872014
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_14 plane_1_12_12 plane_3_10_19 194526752133 153753283400 265998687433
      (by decide) p (plane_0_15_14_sound p h0) (plane_1_12_12_sound p h1) (plane_3_10_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_18 plane_1_12_17 plane_3_11_19 13408722488 30493944443 39890497256
      (by decide) p (plane_0_15_18_sound p h0) (plane_1_12_17_sound p h1) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_16 plane_3_12_14 146319229738 73682118402 82927771297
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_16_sound p h2) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_16 plane_3_13_14 75562747242 61448867834 82927771297
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_16_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_8_16 plane_3_14_14 plane_3_14_15 71509664711 53876670249 6294126022
      (by decide) p (plane_2_8_16_sound p h2) (plane_3_14_14_sound p h3) (plane_3_14_15_sound p h3))
  · refine ⟨(216 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row216]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_15_12_12 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 15)
    (e1 : labels 1 = 12)
    (e2 : labels 2 = 12)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 15 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 12 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 12 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_0_6 plane_3_0_8 23566478669 427660489 46569354854
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_0_6_sound p h3) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_1_7 plane_3_1_9 527155870326 10571859773 1039767016309
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_1_7_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_2_7 plane_3_2_10 64367991506 753968011 122820427970
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_2_7_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_3_11 48098237513 249168225957 565595488056
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_4_10 281228124047 5195400765 141398872014
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_5_11 plane_3_5_13 112810242211 3977652280 219687422719
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_5_11_sound p h3) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_6_11 plane_3_6_14 275073929313 19888261400 542395821437
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_6_11_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_7_15 6587121193 282585774453 565595488056
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_8_13 plane_3_8_16 35158011431 35595460851 12025043673
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_9_15 281228124047 5195400765 141398872014
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_12_12 plane_2_12_12 plane_3_10_19 265998687433 194526752133 214074416447
      (by decide) p (plane_1_12_12_sound p h1) (plane_2_12_12_sound p h2) (plane_3_10_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_12_12 plane_3_11_19 8438500783 95375342880 82927771297
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_12_12_sound p h2) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_12_14 plane_3_12_18 175718623442 21681977787 73682118402
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_12_14_sound p h3) (plane_3_12_18_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_13_14 plane_3_13_19 187214839747 5131925868 92173301751
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_13_14_sound p h3) (plane_3_13_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_1 plane_1_12_12 plane_3_14_19 108426769676000000 268211 232722
      (by decide) p (plane_0_15_1_sound p h0) (plane_1_12_12_sound p h1) (plane_3_14_19_sound p h3))
  · refine ⟨(217 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row217]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_15_13_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 15)
    (e1 : labels 1 = 13)
    (e2 : labels 2 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 15 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 8 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_0_6 1124082257821 10263851736 568648995369
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_1_9 67699997 286092288567 568648995369
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_2_10 1151283961 42377682852 81235570767
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_3_11 48098237513 249168225957 565595488056
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_4 plane_3_4_10 1131762613157 20781603060 568648995369
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_4_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_5_11 plane_3_5_13 112810242211 3977652280 219687422719
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_5_11_sound p h3) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_3_6_11 plane_3_6_14 275073929313 19888261400 542395821437
      (by decide) p (plane_0_15_17_sound p h0) (plane_3_6_11_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_7_15 6587121193 282585774453 565595488056
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_3_8_13 plane_3_8_16 35158011431 35595460851 12025043673
      (by decide) p (plane_0_15_15_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_3_9_15 281228124047 5195400765 141398872014
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_14 plane_1_13_16 plane_3_10_19 27631156413 19219160425 16091708513
      (by decide) p (plane_0_15_14_sound p h0) (plane_1_13_16_sound p h1) (plane_3_10_19_sound p h3))
  · refine ⟨(218 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row218]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_16 plane_3_12_14 146319229738 73682118402 82927771297
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_16_sound p h2) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_8_16 plane_3_13_14 75562747242 61448867834 82927771297
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_8_16_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_12 plane_3_14_14 plane_3_14_19 286195087637 207193100746 208382902691
      (by decide) p (plane_1_13_12_sound p h1) (plane_3_14_14_sound p h3) (plane_3_14_19_sound p h3))
  · refine ⟨(219 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row219]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_15_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 15)
    (e1 : labels 1 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 15 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_1_8_16 plane_2_0_8 249168225957 2226553614 492686929159
      (by decide) p (plane_0_15_17_sound p h0) (plane_1_8_16_sound p h1) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_1_8_16 plane_2_1_9 249154618709 1917121227 492686929159
      (by decide) p (plane_0_15_17_sound p h0) (plane_1_8_16_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_2_2_4 plane_2_2_10 293123962594 4966236753 558968563873
      (by decide) p (plane_0_15_17_sound p h0) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_2_3_6 61200344185 5028270933 70699436007
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_1_8_16 plane_2_4_12 245232080481 18920357693 492686929159
      (by decide) p (plane_0_15_17_sound p h0) (plane_1_8_16_sound p h1) (plane_2_4_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_2_5_13 3615241625 145011768897 282797744028
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_6_8 plane_2_6_14 288682233706 145011768897 6345271797
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_6_8_sound p h2) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_7_9 plane_2_7_19 1104672086663 568648995369 20220009861
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_7_9_sound p h2) (plane_2_7_19_sound p h2))
  · exact complete_15_8_8 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_15_14 plane_1_8_16 plane_2_9_17 257938437109 201389209616 265998687433
      (by decide) p (plane_0_15_14_sound p h0) (plane_1_8_16_sound p h1) (plane_2_9_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_10_13 plane_2_10_18 283358547227 286123403553 108281777256
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_10_13_sound p h2) (plane_2_10_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_11_13 plane_2_11_19 94908832430 47692487307 2115090599
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact complete_15_8_12 labels p h e0 e1 he
  · exact complete_15_8_13 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_15_1 plane_0_15_15 plane_2_14_17 130381689316000000 173613 178307
      (by decide) p (plane_0_15_1_sound p h0) (plane_0_15_15_sound p h0) (plane_2_14_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_1 plane_0_15_15 plane_2_15_17 8906214456000000 1057261 534921
      (by decide) p (plane_0_15_1_sound p h0) (plane_0_15_15_sound p h0) (plane_2_15_17_sound p h2))

theorem complete_15_12 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 15)
    (e1 : labels 1 = 12)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 15 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 12 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_15_3 plane_0_15_17 plane_2_0_8 8906214456000000 534921 1057261
      (by decide) p (plane_0_15_3_sound p h0) (plane_0_15_17_sound p h0) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_2_1_4 plane_2_1_9 286195087637 1917121227 565096908217
      (by decide) p (plane_0_15_17_sound p h0) (plane_2_1_4_sound p h2) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_2_2_4 plane_2_2_10 293123962594 4966236753 558968563873
      (by decide) p (plane_0_15_17_sound p h0) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_2_3_6 61200344185 5028270933 70699436007
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_3 plane_0_15_17 plane_2_4_12 75681430772000000 528190 1057261
      (by decide) p (plane_0_15_3_sound p h0) (plane_0_15_17_sound p h0) (plane_2_4_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_2_5_13 3615241625 145011768897 282797744028
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_6_8 plane_2_6_14 288682233706 145011768897 6345271797
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_6_8_sound p h2) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_7_9 plane_2_7_19 1104672086663 568648995369 20220009861
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_7_9_sound p h2) (plane_2_7_19_sound p h2))
  · exact complete_15_12_8 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_12_17 plane_2_9_12 plane_2_9_17 284027168089 41390492312 225578898288
      (by decide) p (plane_1_12_17_sound p h1) (plane_2_9_12_sound p h2) (plane_2_9_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_10_13 plane_2_10_18 283358547227 286123403553 108281777256
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_10_13_sound p h2) (plane_2_10_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_11_13 plane_2_11_19 94908832430 47692487307 2115090599
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact complete_15_12_12 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_12_12 plane_2_13_12 plane_2_13_16 219550877952 56954921416 157119495031
      (by decide) p (plane_1_12_12_sound p h1) (plane_2_13_12_sound p h2) (plane_2_13_16_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_1 plane_0_15_15 plane_2_14_17 130381689316000000 173613 178307
      (by decide) p (plane_0_15_1_sound p h0) (plane_0_15_15_sound p h0) (plane_2_14_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_1 plane_0_15_15 plane_2_15_17 8906214456000000 1057261 534921
      (by decide) p (plane_0_15_1_sound p h0) (plane_0_15_15_sound p h0) (plane_2_15_17_sound p h2))

theorem complete_15_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 15)
    (e1 : labels 1 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 15 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_15_3 plane_0_15_17 plane_2_0_8 8906214456000000 534921 1057261
      (by decide) p (plane_0_15_3_sound p h0) (plane_0_15_17_sound p h0) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_2_1_4 plane_2_1_9 286195087637 1917121227 565096908217
      (by decide) p (plane_0_15_17_sound p h0) (plane_2_1_4_sound p h2) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_2_2_4 plane_2_2_10 293123962594 4966236753 558968563873
      (by decide) p (plane_0_15_17_sound p h0) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_2_3_6 61200344185 5028270933 70699436007
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_1_13_18 plane_2_4_12 92227723283 18920357693 203266315391
      (by decide) p (plane_0_15_17_sound p h0) (plane_1_13_18_sound p h1) (plane_2_4_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_2_5_13 3615241625 145011768897 282797744028
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_6_8 plane_2_6_14 288682233706 145011768897 6345271797
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_6_8_sound p h2) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_7_6 plane_2_7_19 77676143209 81235570767 29793878061
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_7_6_sound p h2) (plane_2_7_19_sound p h2))
  · exact complete_15_13_8 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_15_14 plane_2_9_12 plane_2_9_17 40575309727 28769887088 30598113403
      (by decide) p (plane_0_15_14_sound p h0) (plane_2_9_12_sound p h2) (plane_2_9_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_10_13 plane_2_10_18 283358547227 286123403553 108281777256
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_10_13_sound p h2) (plane_2_10_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_2_11_13 plane_2_11_19 94908832430 47692487307 2115090599
      (by decide) p (plane_0_15_15_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_13_12 plane_1_13_16 plane_2_12_12 56954921416 157119495031 219550877952
      (by decide) p (plane_1_13_12_sound p h1) (plane_1_13_16_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_14 plane_1_13_12 plane_2_13_12 109849895569 415576003437 394732355537
      (by decide) p (plane_0_15_14_sound p h0) (plane_1_13_12_sound p h1) (plane_2_13_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_1_13_12 plane_2_14_17 64860288389 32595422329 91242654311
      (by decide) p (plane_0_15_15_sound p h0) (plane_1_13_12_sound p h1) (plane_2_14_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_1_13_16 plane_2_15_17 245640855940 1113276807 124206230292
      (by decide) p (plane_0_15_15_sound p h0) (plane_1_13_16_sound p h1) (plane_2_15_17_sound p h2))

theorem complete_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 15 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_1_0_8 94251122451 677744907 94265914676
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_1_0_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_1_1_9 188479610895 1407478171 188531829352
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_1_1_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_1_2_10 97720717173 59675557 94265914676
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_1_2_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_1_3_6 8825686993 31051557573 70699436007
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_1_3_6_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_15_1 plane_0_15_15 plane_1_4_12 17780407332000000 528190 534921
      (by decide) p (plane_0_15_1_sound p h0) (plane_0_15_15_sound p h0) (plane_1_4_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_1_5_13 286489913177 4460421057 282797744028
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_1_5_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_0_15_17 plane_1_6_14 286489913177 4460421057 282797744028
      (by decide) p (plane_0_15_15_sound p h0) (plane_0_15_17_sound p h0) (plane_1_6_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_15_15 plane_1_7_8 plane_1_7_19 1676082744797 378632391 843301167081
      (by decide) p (plane_0_15_15_sound p h0) (plane_1_7_8_sound p h1) (plane_1_7_19_sound p h1))
  · exact complete_15_8 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_15_14 plane_0_15_15 plane_1_9_17 179026671 148185826108 143061215619
      (by decide) p (plane_0_15_14_sound p h0) (plane_0_15_15_sound p h0) (plane_1_9_17_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_1_10_13 plane_1_10_18 283358547227 565438832685 224151785744
      (by decide) p (plane_0_15_17_sound p h0) (plane_1_10_13_sound p h1) (plane_1_10_18_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_15_17 plane_1_11_13 plane_1_11_19 284726497290 282753367353 22752306341
      (by decide) p (plane_0_15_17_sound p h0) (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1))
  · exact complete_15_12 labels p h e0 he
  · exact complete_15_13 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_15_3 plane_0_15_17 plane_1_14_17 813065261564000000 520839 1057261
      (by decide) p (plane_0_15_3_sound p h0) (plane_0_15_17_sound p h0) (plane_1_14_17_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_15_3 plane_0_15_17 plane_1_15_17 93400000000 1 1
      (by decide) p (plane_0_15_3_sound p h0) (plane_0_15_17_sound p h0) (plane_1_15_17_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_15
