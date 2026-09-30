import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 5.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_5_2_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 2)
    (e2 : labels 2 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 2 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_2_11 plane_2_2_11 plane_3_0_9 394732355537 415576003437 109849895569
      (by decide) p (plane_1_2_11_sound p h1) (plane_2_2_11_sound p h2) (plane_3_0_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_1_2_11 plane_3_1_9 208382902691 286058466951 273581663960
      (by decide) p (plane_0_5_5_sound p h0) (plane_1_2_11_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_2_10 plane_3_2_4 97720717173 1655412251 51249358108
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_2_10_sound p h2) (plane_3_2_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_2_10 plane_3_3_5 546434044369 66771606715 307496148648
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_2_10_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_2_11 plane_3_4_4 plane_3_4_9 286122431238 121004392604 273727962933
      (by decide) p (plane_2_2_11_sound p h2) (plane_3_4_4_sound p h3) (plane_3_4_9_sound p h3))
  · refine ⟨(54 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row54]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_2_10 plane_3_6_8 295155055633 10415553607 153748074324
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_2_10_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_2_10 plane_3_7_9 576554357591 28457152733 307496148648
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_2_10_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_2_10 plane_3_8_4 8058987727 589557157165 307496148648
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_2_10_sound p h2) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_2_10 plane_3_9_9 5338712606 289889229815 296584132177
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_2_10_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_2_10 plane_3_10_10 5338712606 289889229815 296584132177
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_2_10_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_2_10 plane_3_11_13 295155055633 10415553607 153748074324
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_2_10_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_2_10 plane_3_12_12 29600136713 258269678195 307496148648
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_2_10_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_2_10 plane_3_13_13 1813877443 153758773765 153748074324
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_2_10_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_2_10 plane_3_14_14 520176509 286058466951 296584132177
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_2_10_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_2_10 plane_3_15_15 358053342 286092288567 296584132177
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_2_10_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_5_2_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 2)
    (e2 : labels 2 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 6 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_6_6 plane_3_0_8 59675557 49436485637 51249358108
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_6_6_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_6_6 plane_3_1_9 520176509 296584132177 307496148648
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_6_6_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_3_2_4 plane_3_2_10 293123962594 153758773765 4966236753
      (by decide) p (plane_1_2_10_sound p h1) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_6_14 plane_3_3_5 532335567341 66771606715 300648190012
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_6_14_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(55 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row55]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(56 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row56]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_3_6_8 plane_3_6_14 288682233706 150282144431 10415553607
      (by decide) p (plane_1_2_10_sound p h1) (plane_3_6_8_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_3_7_9 plane_3_7_19 1104672086663 589557157165 28457152733
      (by decide) p (plane_1_2_10_sound p h1) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_15 plane_3_8_8 plane_3_8_13 30219441171 11497565201 31203773929
      (by decide) p (plane_2_6_15_sound p h2) (plane_3_8_8_sound p h3) (plane_3_8_13_sound p h3))
  · refine ⟨(57 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row57]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_3_10_10 plane_3_10_17 140046111449 95728368055 150282144431
      (by decide) p (plane_1_2_10_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_3_11_13 plane_3_11_19 284726497290 148309456911 10415553607
      (by decide) p (plane_1_2_10_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_6_14 plane_3_12_12 21478273037 258269678195 300648190012
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_6_14_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_6_14 plane_3_13_13 5338712606 296610908583 289994215265
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_6_14_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_6_14 plane_3_14_14 9078349777 286058466951 289994215265
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_6_14_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_6_14 plane_3_15_17 286489913177 4966236753 150324095006
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_6_14_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_5_2_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 2)
    (e2 : labels 2 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 7 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(58 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row58]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_7_7 plane_3_1_9 25176504088 286058466951 248740136971
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_7_7_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_3_2_4 plane_3_2_10 293123962594 153758773765 4966236753
      (by decide) p (plane_1_2_10_sound p h1) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_7_19 plane_3_3_5 1047812442533 66771606715 589503107161
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_7_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(59 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row59]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(60 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row60]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_7_19 plane_3_6_8 1131762613157 20831107214 589503107161
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_7_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_7_19 plane_3_7_9 1105418740127 28457152733 589503107161
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_7_19_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_7_15 plane_3_8_8 12743111940 292938243343 292859327197
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_7_15_sound p h2) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_7_10 plane_2_7_15 plane_3_9_8 31203773929 11497565201 30219441171
      (by decide) p (plane_2_7_10_sound p h2) (plane_2_7_15_sound p h2) (plane_3_9_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_3_10_10 plane_3_10_17 140046111449 95728368055 150282144431
      (by decide) p (plane_1_2_10_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_7_19 plane_3_11_13 1131762613157 20831107214 589503107161
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_7_19_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_7_19 plane_3_12_12 57673997591 258269678195 589503107161
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_7_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_7_15 plane_3_13_13 8417041069 307517547530 292859327197
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_7_15_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_7_19 plane_3_14_14 67699997 296584132177 589503107161
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_7_19_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_7_19 plane_3_15_17 1124082257821 9932473506 589503107161
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_7_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_5_2_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 2)
    (e2 : labels 2 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 11 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_11_11 plane_3_0_8 4445101833 286092288567 282458329541
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_11_11_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_11_11 plane_3_1_9 4290134510 286058466951 282458329541
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_11_11_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_11 plane_3_2_10 plane_3_2_12 585143809623 541387309342 8417041069
      (by decide) p (plane_2_11_11_sound p h2) (plane_3_2_10_sound p h3) (plane_3_2_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_11_19 plane_3_3_5 526311269997 66771606715 296643779964
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_11_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(61 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row61]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_11_10 plane_3_5_8 plane_3_5_13 3204302063 3099650918 1170482995
      (by decide) p (plane_2_11_10_sound p h2) (plane_3_5_8_sound p h3) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_11_19 plane_3_6_8 284607575403 10415553607 148321889982
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_11_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_11_11 plane_3_7_17 541387309342 579624683659 292859327197
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_11_11_sound p h2) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_6 plane_3_8_8 plane_3_8_13 90658323513 70761576674 63443117992
      (by decide) p (plane_0_5_6_sound p h0) (plane_3_8_8_sound p h3) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_9 plane_2_11_10 plane_3_9_8 21350669565 8154722029 22367449111
      (by decide) p (plane_1_2_9_sound p h1) (plane_2_11_10_sound p h2) (plane_3_9_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_3_10_10 plane_3_10_17 140046111449 95728368055 150282144431
      (by decide) p (plane_1_2_10_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_3_11_13 plane_3_11_19 284726497290 148309456911 10415553607
      (by decide) p (plane_1_2_10_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_4 plane_1_2_10 plane_3_12_12 258269678195 58966354913 586247925188
      (by decide) p (plane_1_2_4_sound p h1) (plane_1_2_10_sound p h1) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_4 plane_1_2_10 plane_3_13_13 153758773765 4966236753 293123962594
      (by decide) p (plane_1_2_4_sound p h1) (plane_1_2_10_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_4 plane_1_2_10 plane_3_14_14 296584132177 1917121227 586247925188
      (by decide) p (plane_1_2_4_sound p h1) (plane_1_2_10_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_11_19 plane_3_15_17 94251122451 1655412251 49440629994
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_11_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_5_3_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 3)
    (e2 : labels 2 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 3 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 7 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(62 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row62]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_7_7 plane_3_1_9 25176504088 286058466951 248740136971
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_7_7_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_7_6 plane_3_2_4 plane_3_2_10 586247925188 286601706769 422081433215
      (by decide) p (plane_2_7_6_sound p h2) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_7_6 plane_3_3_5 plane_3_3_11 226264453585 129701549796 223245267043
      (by decide) p (plane_2_7_6_sound p h2) (plane_3_3_5_sound p h3) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_1_3_6 plane_3_4_4 40226167464 286092288567 248405159872
      (by decide) p (plane_0_5_5_sound p h0) (plane_1_3_6_sound p h1) (plane_3_4_4_sound p h3))
  · refine ⟨(63 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row63]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_3_11 plane_2_7_19 plane_3_6_8 1131762613157 68452719217 494400306438
      (by decide) p (plane_1_3_11_sound p h1) (plane_2_7_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_7_6 plane_3_7_9 plane_3_7_15 274239687916 138253947245 216155984859
      (by decide) p (plane_2_7_6_sound p h2) (plane_3_7_9_sound p h3) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_1_3_6 plane_3_8_8 32383189320 282557077259 248405159872
      (by decide) p (plane_0_5_5_sound p h0) (plane_1_3_6_sound p h1) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_1_3_6 plane_3_9_9 44927628456 289889229815 248405159872
      (by decide) p (plane_0_5_5_sound p h0) (plane_1_3_6_sound p h1) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_3_6 plane_3_10_10 plane_3_10_17 140046111449 134276751088 22463814228
      (by decide) p (plane_1_3_6_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_3_11 plane_2_7_19 plane_3_11_13 1131762613157 68452719217 494400306438
      (by decide) p (plane_1_3_11_sound p h1) (plane_2_7_19_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_7_19 plane_3_12_12 57673997591 252961440741 576194818729
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_7_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_7_15 plane_3_13_13 plane_3_13_14 292231582690 273061638778 8417041069
      (by decide) p (plane_2_7_15_sound p h2) (plane_3_13_13_sound p h3) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_17 plane_2_7_19 plane_3_14_14 67699997 586500138398 1165751975894
      (by decide) p (plane_0_5_17_sound p h0) (plane_2_7_19_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_7_19 plane_3_15_15 378632391 289926042144 576194818729
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_7_19_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_5_5_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 6 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_5_6 plane_3_0_6 plane_3_0_8 282797744028 94168568283 275461549151
      (by decide) p (plane_1_5_6_sound p h1) (plane_3_0_6_sound p h3) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_6_6 plane_3_1_9 27377711 15262853435 15823588948
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_6_6_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_10 plane_3_2_4 plane_3_2_10 146561981297 29015202855 140213892952
      (by decide) p (plane_1_5_10_sound p h1) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_6_14 plane_3_3_5 28017661439 3934394987 15474998134
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_6_14_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(64 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row64]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_5_6 plane_1_5_10 plane_3_5_13 52496582228 97785562203 146115791345
      (by decide) p (plane_1_5_6_sound p h1) (plane_1_5_10_sound p h1) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_10 plane_1_5_13 plane_3_6_13 94515900045 108257512397 144488640871
      (by decide) p (plane_1_5_10_sound p h1) (plane_1_5_13_sound p h1) (plane_3_6_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_3_7_9 plane_3_7_19 1104672086663 576406739029 37825715679
      (by decide) p (plane_0_5_13_sound p h0) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_15 plane_3_8_8 plane_3_8_13 30219441171 11497565201 31203773929
      (by decide) p (plane_2_6_15_sound p h2) (plane_3_8_8_sound p h3) (plane_3_8_13_sound p h3))
  · refine ⟨(65 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row65]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_6_14 plane_3_10_13 1866373621 690744503 1932210548
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_6_14_sound p h2) (plane_3_10_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_3_11_13 plane_3_11_19 47454416215 24160503512 2550867439
      (by decide) p (plane_0_5_13_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_6_14 plane_3_12_12 1130435423 13313760039 15474998134
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_6_14_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_6_14 plane_3_13_13 5338712606 296610908583 289994215265
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_6_14_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_6_14 plane_3_14_14 9078349777 286058466951 289994215265
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_6_14_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_14 plane_3_15_15 plane_3_15_17 282797744028 286489913177 4460421057
      (by decide) p (plane_2_6_14_sound p h2) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_5_5_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 11 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_5_5 plane_2_11_11 plane_3_0_8 4445101833 286123403553 282557077259
      (by decide) p (plane_1_5_5_sound p h1) (plane_2_11_11_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_5 plane_2_11_11 plane_3_1_9 4290134510 286091972249 282557077259
      (by decide) p (plane_1_5_5_sound p h1) (plane_2_11_11_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_11 plane_3_2_10 plane_3_2_12 585143809623 541387309342 8417041069
      (by decide) p (plane_2_11_11_sound p h2) (plane_3_2_10_sound p h3) (plane_3_2_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_13 plane_2_11_19 plane_3_3_5 526311269997 152783593819 569452994580
      (by decide) p (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(66 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row66]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_11_10 plane_3_5_8 plane_3_5_13 3204302063 3099650918 1170482995
      (by decide) p (plane_2_11_10_sound p h2) (plane_3_5_8_sound p h3) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_10 plane_3_6_8 plane_3_6_14 144341116853 69742145655 101798132034
      (by decide) p (plane_2_11_10_sound p h2) (plane_3_6_8_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_10 plane_2_11_11 plane_3_7_17 541387309342 165032430177 271974970539
      (by decide) p (plane_2_11_10_sound p h2) (plane_2_11_11_sound p h2) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_6 plane_3_8_8 plane_3_8_13 90658323513 70761576674 63443117992
      (by decide) p (plane_0_5_6_sound p h0) (plane_3_8_8_sound p h3) (plane_3_8_13_sound p h3))
  · refine ⟨(67 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row67]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_11_13 plane_2_11_19 plane_3_10_13 70440797646 58992250217 142363248645
      (by decide) p (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2) (plane_3_10_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_13 plane_3_11_13 plane_3_11_19 94908832430 94869191801 11099928857
      (by decide) p (plane_2_11_13_sound p h2) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_13 plane_2_11_19 plane_3_12_12 8438500783 165657187841 189817664860
      (by decide) p (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_6 plane_2_11_13 plane_3_13_13 295155055633 97445420627 273901749379
      (by decide) p (plane_0_5_6_sound p h0) (plane_2_11_13_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_11_19 plane_3_14_14 1407478171 95352822317 95374467851
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_11_19_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_13 plane_2_11_19 plane_3_15_17 282753367353 22752306341 284726497290
      (by decide) p (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_5_6_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 6)
    (e2 : labels 2 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 2 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_1_6_11 plane_3_0_9 30598113403 28769887088 40575309727
      (by decide) p (plane_1_6_6_sound p h1) (plane_1_6_11_sound p h1) (plane_3_0_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_8 plane_1_6_6 plane_3_1_9 296584132177 91348355030 296729705558
      (by decide) p (plane_0_5_8_sound p h0) (plane_1_6_6_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_8 plane_0_5_13 plane_3_2_9 10117034367 12250414744 16021510315
      (by decide) p (plane_0_5_8_sound p h0) (plane_0_5_13_sound p h0) (plane_3_2_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_2_10 plane_3_3_5 546434044369 74753504753 300564288862
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_2_10_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_4_9 11412680983 3662680931 11826774948
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_4_9_sound p h3))
  · refine ⟨(68 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row68]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_2_10 plane_3_6_9 146790202854 59270785703 150282144431
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_2_10_sound p h2) (plane_3_6_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_2_10 plane_3_7_9 30344966189 1990827141 15819173098
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_2_10_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_2_10 plane_3_8_4 plane_3_8_6 1123889340121 578265315311 8058987727
      (by decide) p (plane_2_2_10_sound p h2) (plane_3_8_4_sound p h3) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_9_9 157020959 8840126143 9044004372
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_10_10 157020959 8840126143 9044004372
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_2_10 plane_3_11_11 8417041069 286480696885 300564288862
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_2_10_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_2_10 plane_3_12_12 29600136713 252961440741 300564288862
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_2_10_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_2_10 plane_3_13_13 plane_3_13_14 146115791345 144976325411 1813877443
      (by decide) p (plane_2_2_10_sound p h2) (plane_3_13_13_sound p h3) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_14_14 520176509 296584132177 307496148648
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_15_15 59675557 49436485637 51249358108
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_5_6_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 6)
    (e2 : labels 2 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 6 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_6_6 plane_3_0_9 37046456527 25173651202 38437018581
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_6_6_sound p h2) (plane_3_0_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_6_6 plane_3_1_9 27377711 15257327885 15819173098
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_6_6_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_6_6 plane_3_2_9 144976325411 91053309303 150282144431
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_6_6_sound p h2) (plane_3_2_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_6_14 plane_3_3_5 28017661439 3934394987 15474998134
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_6_14_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_3_4_9 plane_3_4_13 144193592835 102667292328 47614852103
      (by decide) p (plane_1_6_6_sound p h1) (plane_3_4_9_sound p h3) (plane_3_4_13_sound p h3))
  · refine ⟨(69 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row69]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_3_6_9 plane_3_6_13 7604665309 4609327155 3119515037
      (by decide) p (plane_0_5_13_sound p h0) (plane_3_6_9_sound p h3) (plane_3_6_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_3_7_9 plane_3_7_19 1104672086663 576406739029 37825715679
      (by decide) p (plane_0_5_13_sound p h0) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_6_14 plane_3_8_13 279203399763 87603658687 300648190012
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_6_14_sound p h2) (plane_3_8_13_sound p h3))
  · refine ⟨(70 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row70]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_6_14 plane_3_10_13 7465494484 3119515037 7737499067
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_6_14_sound p h2) (plane_3_10_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_3_11_13 plane_3_11_19 47454416215 24160503512 2550867439
      (by decide) p (plane_0_5_13_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_6_14 plane_3_12_12 1130435423 13313760039 15474998134
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_6_14_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_6_14 plane_3_13_13 2669356303 153758773765 150324095006
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_6_14_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_6_14 plane_3_14_14 9078349777 296584132177 300648190012
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_6_14_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_14 plane_3_15_15 plane_3_15_17 282797744028 286489913177 4460421057
      (by decide) p (plane_2_6_14_sound p h2) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_5_7_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 7)
    (e2 : labels 2 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 2 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_5_4 plane_2_2_11 plane_3_0_9 394732355537 153753283400 415576003437
      (by decide) p (plane_0_5_4_sound p h0) (plane_2_2_11_sound p h2) (plane_3_0_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_8 plane_1_7_7 plane_3_1_9 248740136971 91348355030 240683185084
      (by decide) p (plane_0_5_8_sound p h0) (plane_1_7_7_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_8 plane_0_5_13 plane_3_2_9 10117034367 12250414744 16021510315
      (by decide) p (plane_0_5_8_sound p h0) (plane_0_5_13_sound p h0) (plane_3_2_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_2_10 plane_3_3_5 546434044369 74753504753 300564288862
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_2_10_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_2_11 plane_3_4_4 plane_3_4_9 286122431238 121004392604 273727962933
      (by decide) p (plane_2_2_11_sound p h2) (plane_3_4_4_sound p h3) (plane_3_4_9_sound p h3))
  · refine ⟨(71 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row71]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_2_10 plane_3_6_9 146790202854 59270785703 150282144431
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_2_10_sound p h2) (plane_3_6_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_2_10 plane_3_7_9 30344966189 1990827141 15819173098
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_2_10_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_2_10 plane_3_8_4 8058987727 1130273258965 589503107161
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_2_10 plane_3_9_9 5338712606 289889229815 296584132177
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_2_10_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_2_10 plane_3_10_10 5338712606 289889229815 296584132177
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_2_10_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_2_10 plane_3_11_11 8417041069 561624263596 589503107161
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_2_10 plane_3_12_12 29600136713 495236966130 589503107161
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_2_10 plane_3_13_13 3627754886 589557157165 589503107161
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_2_10 plane_3_14_14 520176509 286058466951 296584132177
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_2_10_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_2_10 plane_3_15_15 358053342 286092288567 296584132177
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_2_10_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_5_7_3 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 7)
    (e2 : labels 2 = 3)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 3 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_5_4 plane_2_3_11 plane_3_0_9 265998687433 153753283400 194526752133
      (by decide) p (plane_0_5_4_sound p h0) (plane_2_3_11_sound p h2) (plane_3_0_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_8 plane_1_7_7 plane_3_1_9 248740136971 91348355030 240683185084
      (by decide) p (plane_0_5_8_sound p h0) (plane_1_7_7_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_8 plane_0_5_13 plane_3_2_9 10117034367 12250414744 16021510315
      (by decide) p (plane_0_5_8_sound p h0) (plane_0_5_13_sound p h0) (plane_3_2_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_3_11 plane_3_3_5 464134193302 74753504753 251662704291
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_3_11_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_3_4_4 plane_3_4_9 13624877678 9858040810 9931292687
      (by decide) p (plane_1_7_6_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_9_sound p h3))
  · refine ⟨(72 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row72]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_3_11 plane_3_6_9 256288378439 118541571406 251662704291
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_3_11_sound p h2) (plane_3_6_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_3_7_9 plane_3_7_19 1104672086663 576406739029 37825715679
      (by decide) p (plane_0_5_13_sound p h0) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_3_8_8 plane_3_8_13 30219441171 22187052214 23785606991
      (by decide) p (plane_1_7_6_sound p h1) (plane_3_8_8_sound p h3) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_2_3_10 plane_3_9_9 257725126726 206735075835 483517335397
      (by decide) p (plane_1_7_6_sound p h1) (plane_2_3_10_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_7_6 plane_3_10_10 10880793465 15457684384 14413930903
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_7_6_sound p h1) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_3_11_13 plane_3_11_19 47454416215 24160503512 2550867439
      (by decide) p (plane_0_5_13_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_3_12_12 plane_3_12_14 481515535842 343368295236 209222168489
      (by decide) p (plane_1_7_6_sound p h1) (plane_3_12_12_sound p h3) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_1_7_19 plane_3_13_13 589557157165 219913888843 543733002463
      (by decide) p (plane_1_7_6_sound p h1) (plane_1_7_19_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_1_7_19 plane_3_14_14 568581733094 208382902691 543733002463
      (by decide) p (plane_1_7_6_sound p h1) (plane_1_7_19_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_3_11 plane_3_15_15 8438500783 189549665123 164800102146
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_3_11_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_5_7_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 7)
    (e2 : labels 2 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 7 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(73 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row73]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_2_7_7 plane_3_1_9 25176504088 286058466951 248740136971
      (by decide) p (plane_0_5_5_sound p h0) (plane_2_7_7_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_7_6 plane_3_2_4 plane_3_2_10 586247925188 286601706769 422081433215
      (by decide) p (plane_2_7_6_sound p h2) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_7_6 plane_3_3_5 plane_3_3_11 226264453585 129701549796 223245267043
      (by decide) p (plane_2_7_6_sound p h2) (plane_3_3_5_sound p h3) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_3_4_4 plane_3_4_9 13624877678 9858040810 9931292687
      (by decide) p (plane_1_7_6_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_9_sound p h3))
  · refine ⟨(74 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row74]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_7_10 plane_2_7_6 plane_3_6_8 144985059017 179698247865 108799280122
      (by decide) p (plane_1_7_10_sound p h1) (plane_2_7_6_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_7_6 plane_3_7_9 plane_3_7_15 274239687916 138253947245 216155984859
      (by decide) p (plane_2_7_6_sound p h2) (plane_3_7_9_sound p h3) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_3_8_8 plane_3_8_13 30219441171 22187052214 23785606991
      (by decide) p (plane_1_7_6_sound p h1) (plane_3_8_8_sound p h3) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_2_7_10 plane_3_9_9 93067799921 68911691945 108799280122
      (by decide) p (plane_1_7_6_sound p h1) (plane_2_7_10_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_7_6 plane_3_10_10 10880793465 15457684384 14413930903
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_7_6_sound p h1) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_7_19 plane_3_11_13 1131762613157 30610409268 576194818729
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_7_19_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_7_19 plane_3_12_12 57673997591 495236966130 1130136737677
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_7_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_1_7_19 plane_3_13_13 589557157165 219913888843 543733002463
      (by decide) p (plane_1_7_6_sound p h1) (plane_1_7_19_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_7_19 plane_3_14_14 67699997 568581733094 1130136737677
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_7_19_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_7_19 plane_3_15_15 378632391 568648995369 1130136737677
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_7_19_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_5_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_5_8 plane_1_2_10 plane_2_0_6 1507936022 282393737915 148364852779
      (by decide) p (plane_0_5_8_sound p h0) (plane_1_2_10_sound p h1) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_1_2_11 plane_2_1_7 461550255767 60329575017 284027168089
      (by decide) p (plane_1_2_10_sound p h1) (plane_1_2_11_sound p h1) (plane_2_1_7_sound p h2))
  · exact complete_5_2_2 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_5_4 plane_1_2_11 plane_2_3_11 157119495031 194526752133 394732355537
      (by decide) p (plane_0_5_4_sound p h0) (plane_1_2_11_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_4_4 plane_2_4_10 142363248645 3467060182 74160944991
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_5_5 plane_2_5_11 556142498998 21657103543 296610908583
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_5_5_sound p h2) (plane_2_5_11_sound p h2))
  · exact complete_5_2_6 labels p h e0 e1 he
  · exact complete_5_2_7 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_8_4 plane_2_8_14 1104672086663 21657103543 589503107161
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_9_9 plane_2_9_15 144341116853 3467060182 75162047503
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_9 plane_2_10_10 plane_2_10_15 16021510315 12250414744 10117034367
      (by decide) p (plane_1_2_9_sound p h1) (plane_2_10_10_sound p h2) (plane_2_10_15_sound p h2))
  · exact complete_5_2_11 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_12_12 plane_2_12_18 452528907170 60329575017 257938437109
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_13_13 plane_2_13_19 146561981297 753968011 76874037162
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_4 plane_1_2_10 plane_2_14_14 296610908583 10571859773 586247925188
      (by decide) p (plane_1_2_4_sound p h1) (plane_1_2_10_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_4 plane_1_2_10 plane_2_15_15 74160944991 2565962934 146561981297
      (by decide) p (plane_1_2_4_sound p h1) (plane_1_2_10_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_5_3 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 3)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 3 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_3_11 plane_2_0_6 plane_2_0_8 565595488056 249168225957 48098237513
      (by decide) p (plane_1_3_11_sound p h1) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_4 plane_1_3_11 plane_2_1_7 3481536161 565454524009 265998687433
      (by decide) p (plane_0_5_4_sound p h0) (plane_1_3_11_sound p h1) (plane_2_1_7_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_4 plane_1_3_11 plane_2_2_11 157119495031 415576003437 265998687433
      (by decide) p (plane_0_5_4_sound p h0) (plane_1_3_11_sound p h1) (plane_2_2_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_4 plane_1_3_11 plane_2_3_11 214074416447 194526752133 265998687433
      (by decide) p (plane_0_5_4_sound p h0) (plane_1_3_11_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_3_11 plane_2_4_10 plane_2_4_12 561792632189 245232080481 39328026361
      (by decide) p (plane_1_3_11_sound p h1) (plane_2_4_10_sound p h2) (plane_2_4_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_3_11 plane_2_5_11 plane_2_5_13 564051211055 252961440741 31598666101
      (by decide) p (plane_1_3_11_sound p h1) (plane_2_5_11_sound p h2) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_3_6 plane_1_3_11 plane_2_6_11 16803157013 37596483048 36591812992
      (by decide) p (plane_1_3_6_sound p h1) (plane_1_3_11_sound p h1) (plane_2_6_11_sound p h2))
  · exact complete_5_3_7 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_3_5 plane_1_3_11 plane_2_8_14 31598666101 1018382834983 452528907170
      (by decide) p (plane_1_3_5_sound p h1) (plane_1_3_11_sound p h1) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_3_10 plane_2_9_9 plane_2_9_15 144341116853 127460173304 83419324117
      (by decide) p (plane_1_3_10_sound p h1) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_1_3_6 plane_2_10_10 33029106456 289994215265 248405159872
      (by decide) p (plane_0_5_5_sound p h0) (plane_1_3_6_sound p h1) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_1_3_6 plane_2_11_11 43574758200 282458329541 248405159872
      (by decide) p (plane_0_5_5_sound p h0) (plane_1_3_6_sound p h1) (plane_2_11_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_3_10 plane_2_12_12 plane_2_12_18 90505781434 105072273389 62978671705
      (by decide) p (plane_1_3_10_sound p h1) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_3_6 plane_2_13_13 plane_2_13_19 146561981297 122820427970 10347623078
      (by decide) p (plane_1_3_6_sound p h1) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_3_5 plane_2_14_14 65326480587 289994215265 532335567341
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_3_5_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_3_5 plane_2_15_13 plane_2_15_15 569452994580 65045933361 979437441292
      (by decide) p (plane_1_3_5_sound p h1) (plane_2_15_13_sound p h2) (plane_2_15_15_sound p h2))

theorem complete_5_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_5_15 plane_2_0_6 plane_2_0_8 47132957338 25892303767 92085352899
      (by decide) p (plane_1_5_15_sound p h1) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_5_5 plane_1_5_11 plane_2_1_9 28422632345 286058466951 556142498998
      (by decide) p (plane_1_5_5_sound p h1) (plane_1_5_11_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_5_5 plane_1_5_11 plane_2_2_10 21657103543 296610908583 556142498998
      (by decide) p (plane_1_5_5_sound p h1) (plane_1_5_11_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_5_11 plane_2_3_11 31598666101 251662704291 562892190155
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_5_11_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_4_4 plane_2_4_10 94908832430 551711303 48337256299
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_5_11 plane_2_5_10 539721563041 104993164456 562892190155
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_5_11_sound p h1) (plane_2_5_10_sound p h2))
  · exact complete_5_5_6 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_5_6 plane_2_7_10 plane_2_7_15 90658323513 63443117992 70761576674
      (by decide) p (plane_1_5_6_sound p h1) (plane_2_7_10_sound p h2) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_8_4 plane_2_8_14 1104672086663 11163951429 576194818729
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_10 plane_0_5_13 plane_2_9_10 94515900045 108257512397 144488640871
      (by decide) p (plane_0_5_10_sound p h0) (plane_0_5_13_sound p h0) (plane_2_9_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_6 plane_0_5_10 plane_2_10_10 52496582228 97785562203 146115791345
      (by decide) p (plane_0_5_6_sound p h0) (plane_0_5_10_sound p h0) (plane_2_10_10_sound p h2))
  · exact complete_5_5_11 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_12_12 plane_2_12_18 452528907170 74753504753 252961440741
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_10 plane_2_13_13 plane_2_13_19 146561981297 140213892952 29015202855
      (by decide) p (plane_0_5_10_sound p h0) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_5 plane_0_5_11 plane_2_14_14 19913735575 286091972249 556142498998
      (by decide) p (plane_0_5_5_sound p h0) (plane_0_5_11_sound p h0) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_6 plane_2_15_15 plane_2_15_17 282797744028 275461549151 94168568283
      (by decide) p (plane_0_5_6_sound p h0) (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2))

theorem complete_5_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_0_6 plane_2_0_8 282797744028 145011768897 3615241625
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_6_11 plane_2_1_9 84016202474 289994215265 279203399763
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_6_11_sound p h1) (plane_2_1_9_sound p h2))
  · exact complete_5_6_2 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_5_8 plane_1_6_6 plane_2_3_6 1591942012 10049054568 11412680983
      (by decide) p (plane_0_5_8_sound p h0) (plane_1_6_6_sound p h1) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_4_4 plane_2_4_10 94908832430 551711303 48337256299
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_5_6 plane_2_5_10 146115791345 52496582228 97785562203
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_5_6_sound p h2) (plane_2_5_10_sound p h2))
  · exact complete_5_6_6 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_7_6 plane_2_7_10 284027168089 90948203851 216547944797
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_7_6_sound p h2) (plane_2_7_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_8_4 plane_2_8_14 1104672086663 11163951429 576194818729
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_10 plane_0_5_13 plane_2_9_10 94515900045 108257512397 144488640871
      (by decide) p (plane_0_5_10_sound p h0) (plane_0_5_13_sound p h0) (plane_2_9_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_6_9 plane_2_10_10 3119515037 7737499067 7465494484
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_6_9_sound p h1) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_1_6_9 plane_2_11_10 100351480326 100955561673 146115791345
      (by decide) p (plane_1_6_6_sound p h1) (plane_1_6_9_sound p h1) (plane_2_11_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_12_12 plane_2_12_18 452528907170 49495462403 251662704291
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_6_8 plane_2_13_13 6934120364 150282144431 288280977931
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_6_8_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_6_8 plane_2_14_14 21090479789 289994215265 576561955862
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_6_8_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_6_8 plane_2_15_13 plane_2_15_15 28472649729 1039080153 55552212773
      (by decide) p (plane_1_6_8_sound p h1) (plane_2_15_13_sound p h2) (plane_2_15_15_sound p h2))

theorem complete_5_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    (e1 : labels 1 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_0_6 plane_2_0_8 282797744028 145011768897 3615241625
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_8 plane_2_1_7 plane_2_1_9 263577935163 47868557605 253947212243
      (by decide) p (plane_0_5_8_sound p h0) (plane_2_1_7_sound p h2) (plane_2_1_9_sound p h2))
  · exact complete_5_7_2 labels p h e0 e1 he
  · exact complete_5_7_3 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_4_4 plane_2_4_10 94908832430 551711303 48337256299
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_7_10 plane_2_5_6 70761576674 65190374802 93067799921
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_7_10_sound p h1) (plane_2_5_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_1_7_10 plane_2_6_6 90948203851 216547944797 284027168089
      (by decide) p (plane_1_7_6_sound p h1) (plane_1_7_10_sound p h1) (plane_2_6_6_sound p h2))
  · exact complete_5_7_7 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_2_8_4 plane_2_8_14 1104672086663 11163951429 576194818729
      (by decide) p (plane_0_5_13_sound p h0) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_7_6 plane_2_9_9 11575386015 15474998134 14413930903
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_7_6_sound p h1) (plane_2_9_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_7_6 plane_2_10_10 11575386015 15474998134 14413930903
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_7_6_sound p h1) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_2_11_11 plane_2_11_13 561792632189 535300478849 201657322281
      (by decide) p (plane_1_7_6_sound p h1) (plane_2_11_11_sound p h2) (plane_2_11_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_1_7_19 plane_2_12_12 494400306438 157119495031 543733002463
      (by decide) p (plane_1_7_6_sound p h1) (plane_1_7_19_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_1_7_19 plane_2_13_13 589503107161 216547944797 543733002463
      (by decide) p (plane_1_7_6_sound p h1) (plane_1_7_19_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_1_7_19 plane_2_14_14 568649365826 212594706109 543733002463
      (by decide) p (plane_1_7_6_sound p h1) (plane_1_7_19_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_7_6 plane_1_7_19 plane_2_15_15 81244543299 30352639179 77676143209
      (by decide) p (plane_1_7_6_sound p h1) (plane_1_7_19_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 5 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_5_6 plane_1_0_6 plane_1_0_8 282797744028 141060621963 181086258647
      (by decide) p (plane_0_5_6_sound p h0) (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_5_6 plane_1_1_6 plane_1_1_9 139669658299 141095471221 41766690707
      (by decide) p (plane_0_5_6_sound p h0) (plane_1_1_6_sound p h1) (plane_1_1_9_sound p h1))
  · exact complete_5_2 labels p h e0 he
  · exact complete_5_3 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_5_11 plane_0_5_13 plane_1_4_9 58574633094 31513008952 112810242211
      (by decide) p (plane_0_5_11_sound p h0) (plane_0_5_13_sound p h0) (plane_1_4_9_sound p h1))
  · exact complete_5_5 labels p h e0 he
  · exact complete_5_6 labels p h e0 he
  · exact complete_5_7 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_5_11 plane_0_5_13 plane_1_8_8 234817143 549569533268 564051211055
      (by decide) p (plane_0_5_11_sound p h0) (plane_0_5_13_sound p h0) (plane_1_8_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_5_10 plane_0_5_13 plane_1_9_10 148796686621 32940028859 144488640871
      (by decide) p (plane_0_5_10_sound p h0) (plane_0_5_13_sound p h0) (plane_1_9_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_5_11 plane_0_5_13 plane_1_10_10 146364030 5925180949 5937381169
      (by decide) p (plane_0_5_11_sound p h0) (plane_0_5_13_sound p h0) (plane_1_10_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_11_11 plane_1_11_13 561792632189 576561955862 234817143
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_11_11_sound p h1) (plane_1_11_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_12_12 plane_1_12_18 452528907170 532335567341 21478273037
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_12_12_sound p h1) (plane_1_12_18_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_5_11 plane_0_5_13 plane_1_13_13 280984874 30344966189 29686905845
      (by decide) p (plane_0_5_11_sound p h0) (plane_0_5_13_sound p h0) (plane_1_13_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_14_14 plane_1_14_16 527155870326 532335567341 9078349777
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_14_14_sound p h1) (plane_1_14_16_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_5_13 plane_1_15_13 plane_1_15_15 284726497290 4460421057 283820556874
      (by decide) p (plane_0_5_13_sound p h0) (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_5
