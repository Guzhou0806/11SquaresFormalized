import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 13.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_13_10_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 0 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_16 plane_3_0_6 122820427970 753968011 64367991506
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_16_sound p h0) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_16 plane_3_1_9 36559912600 296610908583 257471966024
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_16_sound p h0) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_12 plane_2_0_9 plane_3_2_7 7572568712 15704081800 24445647261
      (by decide) p (plane_0_13_12_sound p h0) (plane_2_0_9_sound p h2) (plane_3_2_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_3_3_6 plane_3_3_11 27443859744 7119365177 26251808648
      (by decide) p (plane_0_13_16_sound p h0) (plane_3_3_6_sound p h3) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_3_4_4 plane_3_4_10 142363248645 3467060182 74160944991
      (by decide) p (plane_0_13_13_sound p h0) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_0_8 plane_3_5_6 141060621963 97445420627 148309456911
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_0_8_sound p h2) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_0_8 plane_3_6_6 59675557 51249358108 49436485637
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_0_8_sound p h2) (plane_3_6_6_sound p h3))
  · refine ⟨(186 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row186]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_0_8 plane_3_8_6 26910862015 27927963577 14124710182
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_0_8_sound p h2) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_0_8 plane_3_9_9 4460421057 150324095006 148309456911
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_0_8_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_0_8 plane_3_10_10 4460421057 150324095006 148309456911
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_0_8_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_0_8 plane_3_11_11 4445101833 282458329541 286092288567
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_0_8_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_0_8 plane_3_12_12 1489147197 14631772763 16828958151
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_0_8_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_0_8 plane_3_13_13 59675557 51249358108 49436485637
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_0_8_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_0_8 plane_3_14_14 11632051 817109941 817131994
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_0_8_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_0_8 plane_3_15_15 96820701 7062947142 7062355091
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_0_8_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_13_10_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 4 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_4_4 plane_3_0_6 282753367353 1507936022 148309456911
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_4_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_4_4 plane_3_1_9 4222434513 286091972249 286092288567
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_4_4_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_4 plane_2_4_9 plane_3_2_11 121004392604 273727962933 286122431238
      (by decide) p (plane_2_4_4_sound p h2) (plane_2_4_9_sound p h2) (plane_3_2_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_4 plane_2_4_9 plane_3_3_11 240683185084 25315502349 286122431238
      (by decide) p (plane_2_4_4_sound p h2) (plane_2_4_9_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_3_4_4 plane_3_4_10 142363248645 3467060182 74160944991
      (by decide) p (plane_0_13_13_sound p h0) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_3_5_6 plane_3_5_13 140046111449 150324095006 97445420627
      (by decide) p (plane_0_13_13_sound p h0) (plane_3_5_6_sound p h3) (plane_3_5_13_sound p h3))
  · refine ⟨(187 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row187]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(188 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row188]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_3_8_6 184381206724 586487235117 292231582690
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_3_9_9 plane_3_9_15 144341116853 3467060182 75162047503
      (by decide) p (plane_0_13_13_sound p h0) (plane_3_9_9_sound p h3) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_10_18 plane_3_10_10 289994215265 182106618606 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_10_18_sound p h1) (plane_3_10_10_sound p h3))
  · refine ⟨(189 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row189]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_3_12_17 109228705072 20695246156 146115791345
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_3_13_13 plane_3_13_14 146115791345 77101547654 97445420627
      (by decide) p (plane_0_13_14_sound p h0) (plane_3_13_13_sound p h3) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_10_18 plane_3_14_14 286091972249 184172073764 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_10_18_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_10_18 plane_3_15_15 286123403553 184346603502 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_10_18_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_13_10_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 5 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_5_5 plane_3_0_6 565438832685 3015872044 296584132177
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_5_5_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_5_5 plane_3_1_6 277812578482 101720067329 296584132177
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_5_5_sound p h2) (plane_3_1_6_sound p h3))
  · refine ⟨(190 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row190]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_3_3_6 plane_3_3_11 27443859744 7119365177 26251808648
      (by decide) p (plane_0_13_16_sound p h0) (plane_3_3_6_sound p h3) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_3_4_4 plane_3_4_10 142363248645 3467060182 74160944991
      (by decide) p (plane_0_13_13_sound p h0) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_5_13 plane_3_5_6 144513751499 97445420627 150282144431
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_5_13_sound p h2) (plane_3_5_6_sound p h3))
  · refine ⟨(191 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row191]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(192 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row192]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_5_13 plane_3_8_6 582135485611 586487235117 300564288862
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_5_13_sound p h2) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_3_9_9 plane_3_9_15 144341116853 3467060182 75162047503
      (by decide) p (plane_0_13_13_sound p h0) (plane_3_9_9_sound p h3) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_5_13 plane_3_10_10 365910075 7911794474 7909586549
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_5_13_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_5_13 plane_3_11_11 234817143 292859327197 300564288862
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_5_13_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_5_13 plane_3_12_12 21478273037 248740136971 289889229815
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_5_13_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_5_13 plane_3_13_13 157020959 9044004372 8840126143
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_5_13_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_5_13 plane_3_14_14 9078349777 296610908583 300564288862
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_5_13_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_5_13 plane_3_15_15 4460421057 148321889982 150282144431
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_5_13_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_13_10_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 9 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_9_9 plane_3_0_6 286489913177 1507936022 150282144431
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_9_9_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_9_9 plane_3_1_9 9078349777 286091972249 289889229815
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_9_9_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_9_9 plane_3_2_10 5338712606 296584132177 289889229815
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_9_9_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_9_9 plane_3_3_11 21478273037 257938437109 300564288862
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_9_9_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_3_4_4 plane_3_4_10 142363248645 3467060182 74160944991
      (by decide) p (plane_0_13_13_sound p h0) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_9_9 plane_3_5_10 7465494484 2963297563 7909586549
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_9_9_sound p h2) (plane_3_5_10_sound p h3))
  · refine ⟨(193 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row193]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_9_8 plane_3_7_10 plane_3_7_15 30219441171 31203773929 11497565201
      (by decide) p (plane_2_9_8_sound p h2) (plane_3_7_10_sound p h3) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_3_8_6 184381206724 586487235117 292231582690
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_3_9_9 plane_3_9_15 144341116853 3467060182 75162047503
      (by decide) p (plane_0_13_13_sound p h0) (plane_3_9_9_sound p h3) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_10_18 plane_3_10_10 289994215265 182106618606 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_10_18_sound p h1) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_2_9_8 plane_3_11_10 21350669565 22367449111 8154722029
      (by decide) p (plane_0_13_14_sound p h0) (plane_2_9_8_sound p h2) (plane_3_11_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_9_17 plane_3_12_17 128500785028 20695246156 153758773765
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_9_17_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_3_13_13 plane_3_13_14 146115791345 77101547654 97445420627
      (by decide) p (plane_0_13_14_sound p h0) (plane_3_13_13_sound p h3) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_10_18 plane_3_14_14 286091972249 184172073764 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_10_18_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_10_18 plane_3_15_15 286123403553 184346603502 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_10_18_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_13_13_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 13)
    (e2 : labels 2 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 4 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_4_4 plane_3_0_6 282753367353 1507936022 148309456911
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_4_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_4 plane_3_1_7 plane_3_1_9 1052207326 8428013 1050521497
      (by decide) p (plane_2_4_4_sound p h2) (plane_3_1_7_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_1_13_19 plane_3_2_10 1655412251 51249358108 97720717173
      (by decide) p (plane_0_13_13_sound p h0) (plane_1_13_19_sound p h1) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_1_13_19 plane_3_3_11 58966354913 257938437109 586324303038
      (by decide) p (plane_0_13_13_sound p h0) (plane_1_13_19_sound p h1) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_3_4_4 plane_3_4_10 142363248645 3467060182 74160944991
      (by decide) p (plane_0_13_13_sound p h0) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_1_13_19 plane_3_5_10 280427785904 56302653697 293162151519
      (by decide) p (plane_0_13_13_sound p h0) (plane_1_13_19_sound p h1) (plane_3_5_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_13_14 plane_3_6_15 8154722029 22367449111 20318017992
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_13_14_sound p h1) (plane_3_6_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_14 plane_1_13_18 plane_3_7_15 104793484997 177664844544 279339316598
      (by decide) p (plane_1_13_14_sound p h1) (plane_1_13_18_sound p h1) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_3_8_6 184381206724 586487235117 292231582690
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_3_9_9 plane_3_9_15 144341116853 3467060182 75162047503
      (by decide) p (plane_0_13_13_sound p h0) (plane_3_9_9_sound p h3) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_3_10_10 plane_3_10_15 16021510315 12250414744 10117034367
      (by decide) p (plane_0_13_14_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_15_sound p h3))
  · refine ⟨(194 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row194]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_3_12_17 109228705072 20695246156 146115791345
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_3_13_13 plane_3_13_14 146115791345 77101547654 97445420627
      (by decide) p (plane_0_13_14_sound p h0) (plane_3_13_13_sound p h3) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_12 plane_3_14_14 plane_3_14_19 286195087637 281223749827 4290134510
      (by decide) p (plane_2_4_12_sound p h2) (plane_3_14_14_sound p h3) (plane_3_14_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_3 plane_2_4_12 plane_3_15_15 17780407332000000 534921 528190
      (by decide) p (plane_0_13_3_sound p h0) (plane_2_4_12_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_13_14_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 14)
    (e2 : labels 2 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 14 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 0 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_1_14_14 plane_3_0_6 1917121227 491281711880 248405159872
      (by decide) p (plane_0_13_16_sound p h0) (plane_1_14_14_sound p h1) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_1_14_14 plane_3_1_9 286091972249 36559912600 248405159872
      (by decide) p (plane_0_13_16_sound p h0) (plane_1_14_14_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_2_7 248412460584 40357234280 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_2_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_1_14_14 plane_3_3_11 248740136971 56954921416 248405159872
      (by decide) p (plane_0_13_16_sound p h0) (plane_1_14_14_sound p h1) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_3_4_4 plane_3_4_10 569452994580 12377849851 286123403553
      (by decide) p (plane_1_14_14_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_3_5_5 plane_3_5_11 556142498998 19913735575 286091972249
      (by decide) p (plane_1_14_14_sound p h1) (plane_3_5_5_sound p h3) (plane_3_5_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_6_11 274086016275 88201229486 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_6_11_sound p h3))
  · refine ⟨(195 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row195]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_8_6 565128102315 566664611867 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_9_9 8920842114 289994215265 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_10_10 8920842114 289994215265 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_3 plane_2_0_8 plane_3_11_11 17780407332000000 528190 534921
      (by decide) p (plane_0_13_3_sound p h0) (plane_2_0_8_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_12_7 788225060550 855761983118 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_12_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_13_13 358053342 296584132177 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_14_14 4222434513 286091972249 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_15_15 1355489814 95374467851 95364096189
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_13_14_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 14)
    (e2 : labels 2 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 14 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 4 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_4_4 plane_3_0_6 188502244902 639040409 95364096189
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_4_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_4 plane_3_1_7 plane_3_1_9 1052207326 8428013 1050521497
      (by decide) p (plane_2_4_4_sound p h2) (plane_3_1_7_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_3_2_7 plane_3_2_10 257471966024 296584132177 40357234280
      (by decide) p (plane_1_14_14_sound p h1) (plane_3_2_7_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_4_4 plane_3_3_11 1489147197 14631772763 16828958151
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_4_4_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_3_4_4 plane_3_4_10 569452994580 12377849851 286123403553
      (by decide) p (plane_1_14_14_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_4_4 plane_3_5_11 555849206859 19913735575 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_4_4_sound p h2) (plane_3_5_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_14_14 plane_3_6_11 44100614743 106142365011 141095471221
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_14_14_sound p h1) (plane_3_6_11_sound p h3))
  · refine ⟨(196 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row196]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_14_14 plane_3_8_6 566664611867 184381206724 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_14_14_sound p h1) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_3_9_9 plane_3_9_15 577364467412 12377849851 289994215265
      (by decide) p (plane_1_14_14_sound p h1) (plane_3_9_9_sound p h3) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_3_10_10 plane_3_10_15 16021510315 12250414744 10117034367
      (by decide) p (plane_0_13_14_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_15_sound p h3))
  · refine ⟨(197 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row197]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_14_14 plane_3_12_17 20178617140 109228705072 141095471221
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_14_14_sound p h1) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_14_14 plane_3_13_14 94234583558 77101547654 141095471221
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_14_14_sound p h1) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_12 plane_3_14_14 plane_3_14_19 286195087637 281223749827 4290134510
      (by decide) p (plane_2_4_12_sound p h2) (plane_3_14_14_sound p h3) (plane_3_14_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_3 plane_2_4_12 plane_3_15_15 17780407332000000 534921 528190
      (by decide) p (plane_0_13_3_sound p h0) (plane_2_4_12_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_13_15_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 15)
    (e2 : labels 2 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 15 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 0 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_1_15_15 plane_3_0_6 1113276807 245640855940 124206230292
      (by decide) p (plane_0_13_16_sound p h0) (plane_1_15_15_sound p h1) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_1_15_15 plane_3_1_9 286123403553 36559912600 248412460584
      (by decide) p (plane_0_13_16_sound p h0) (plane_1_15_15_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_1_15_14 plane_3_2_7 27631156413 26251808648 16091708513
      (by decide) p (plane_0_13_16_sound p h0) (plane_1_15_14_sound p h1) (plane_3_2_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_3_3_6 plane_3_3_11 27443859744 7119365177 26251808648
      (by decide) p (plane_0_13_16_sound p h0) (plane_3_3_6_sound p h3) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_3_4_4 plane_3_4_10 94908832430 2115090599 47692487307
      (by decide) p (plane_1_15_15_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_5_6 47020207321 31389522761 47687671440
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_6_6 59675557 49436485637 47687671440
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_6_6_sound p h3))
  · refine ⟨(198 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row198]
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
  · exact False.elim (refutationCheck_sound plane_0_13_3 plane_2_0_8 plane_3_11_11 17780407332000000 528190 534921
      (by decide) p (plane_0_13_3_sound p h0) (plane_2_0_8_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_12_7 26274168685 28514397437 9537534288
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_12_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_13_13 59675557 49436485637 47687671440
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_14_14 1407478171 95374467851 95375342880
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_15_15 225914969 15897495769 15895890480
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_13_15_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 15)
    (e2 : labels 2 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 15 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 4 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_4_4 plane_3_0_6 31417040817 123697423 15895890480
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_4_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_4 plane_3_1_7 plane_3_1_9 1052207326 8428013 1050521497
      (by decide) p (plane_2_4_4_sound p h2) (plane_3_1_7_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_14 plane_2_4_4 plane_3_2_7 41402076764 36841541884 32435075873
      (by decide) p (plane_1_15_14_sound p h1) (plane_2_4_4_sound p h2) (plane_3_2_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_4_4 plane_3_3_11 8438500783 82927771297 95375342880
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_4_4_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_3_4_4 plane_3_4_10 94908832430 2115090599 47692487307
      (by decide) p (plane_1_15_15_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_1_15_17 plane_3_5_6 275461549151 94168568283 282797744028
      (by decide) p (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_14 plane_3_6_6 plane_3_6_11 40575309727 30598113403 28769887088
      (by decide) p (plane_1_15_14_sound p h1) (plane_3_6_6_sound p h3) (plane_3_6_11_sound p h3))
  · refine ⟨(199 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row199]
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
  · exact False.elim (refutationCheck_sound plane_0_13_3 plane_1_15_17 plane_3_11_11 75681430772000000 528190 1057261
      (by decide) p (plane_0_13_3_sound p h0) (plane_1_15_17_sound p h1) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_13 plane_1_15_15 plane_3_12_17 10056541866 112811741032 142363248645
      (by decide) p (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_17 plane_3_13_13 plane_3_13_14 146115791345 275461549151 4966236753
      (by decide) p (plane_1_15_17_sound p h1) (plane_3_13_13_sound p h3) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_17 plane_3_14_14 plane_3_14_19 286195087637 565096908217 1917121227
      (by decide) p (plane_1_15_17_sound p h1) (plane_3_14_14_sound p h3) (plane_3_14_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_13_3 plane_1_15_17 plane_3_15_15 8906214456000000 534921 1057261
      (by decide) p (plane_0_13_3_sound p h0) (plane_1_15_17_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_13_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact complete_13_10_0 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_16 plane_2_1_9 40357234280 296584132177 257471966024
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_16_sound p h0) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_2_4 plane_2_2_10 293123962594 153758773765 4966236753
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_2_3_5 95397689800 13354321343 58446316538
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_2_3_5_sound p h2))
  · exact complete_13_10_4 labels p h e0 e1 he
  · exact complete_13_10_5 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_2_6_8 273901749379 10415553607 146115791345
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_2_6_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_7_6 plane_2_7_19 543733002463 589557157165 219913888843
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_7_6_sound p h2) (plane_2_7_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_10_18 plane_2_8_8 282557077259 177664844544 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_10_18_sound p h1) (plane_2_8_8_sound p h2))
  · exact complete_13_10_9 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_2_10_10 plane_2_10_12 564051211055 529897218896 195571124406
      (by decide) p (plane_0_13_14_sound p h0) (plane_2_10_10_sound p h2) (plane_2_10_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_11_13 plane_2_11_19 284726497290 148309456911 10415553607
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_10_18 plane_2_12_12 249154618709 135560397220 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_10_18_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_10_18 plane_2_13_13 296610908583 191456736110 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_10_18_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_10_18 plane_2_14_14 286058466951 188469167116 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_10_18_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_2_15_17 275461549151 4966236753 146115791345
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_2_15_17_sound p h2))

theorem complete_13_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_1_13_19 plane_2_0_8 1710641956 49436485637 97720717173
      (by decide) p (plane_0_13_13_sound p h0) (plane_1_13_19_sound p h1) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_1_13_19 plane_2_1_9 10571859773 296584132177 586324303038
      (by decide) p (plane_0_13_13_sound p h0) (plane_1_13_19_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_1_13_19 plane_2_2_10 1507936022 153758773765 293162151519
      (by decide) p (plane_0_13_13_sound p h0) (plane_1_13_19_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_2_3_5 95397689800 13354321343 58446316538
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_2_3_5_sound p h2))
  · exact complete_13_13_4 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_13_14 plane_2_5_8 plane_2_5_13 16021510315 10117034367 12250414744
      (by decide) p (plane_1_13_14_sound p h1) (plane_2_5_8_sound p h2) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_2_6_8 273901749379 10415553607 146115791345
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_2_6_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_7_6 plane_2_7_19 543733002463 589557157165 219913888843
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_7_6_sound p h2) (plane_2_7_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_0_13_18 plane_2_8_8 104793484997 177664844544 279339316598
      (by decide) p (plane_0_13_14_sound p h0) (plane_0_13_18_sound p h0) (plane_2_8_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_13_14 plane_2_9_8 22367449111 8154722029 20318017992
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_13_14_sound p h1) (plane_2_9_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_2_10_10 plane_2_10_12 564051211055 529897218896 195571124406
      (by decide) p (plane_0_13_14_sound p h0) (plane_2_10_10_sound p h2) (plane_2_10_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_2_11_13 plane_2_11_19 284726497290 148309456911 10415553607
      (by decide) p (plane_0_13_13_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_0_13_19 plane_2_12_12 58966354913 135560397220 374429679494
      (by decide) p (plane_0_13_14_sound p h0) (plane_0_13_19_sound p h0) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_0_13_19 plane_2_13_13 4966236753 95728368055 187214839747
      (by decide) p (plane_0_13_14_sound p h0) (plane_0_13_19_sound p h0) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_2_14_14 plane_2_14_16 263577935163 238494224500 94234583558
      (by decide) p (plane_0_13_14_sound p h0) (plane_2_14_14_sound p h2) (plane_2_14_16_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_19 plane_1_13_13 plane_2_15_17 1507936022 558968563873 293162151519
      (by decide) p (plane_0_13_19_sound p h0) (plane_1_13_13_sound p h1) (plane_2_15_17_sound p h2))

theorem complete_13_14 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 14)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 14 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact complete_13_14_0 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_1_14_14 plane_2_1_9 286058466951 40357234280 248405159872
      (by decide) p (plane_0_13_16_sound p h0) (plane_1_14_14_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_2_4 plane_2_2_10 586247925188 296610908583 10571859773
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_14_14 plane_2_3_5 65326480587 476988449000 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_14_14_sound p h1) (plane_2_3_5_sound p h2))
  · exact complete_13_14_4 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_1_14_19 plane_2_5_8 257015383608 91348355030 286195087637
      (by decide) p (plane_1_14_14_sound p h1) (plane_1_14_19_sound p h1) (plane_2_5_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_14_14 plane_2_6_8 21090479789 547803498758 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_14_14_sound p h1) (plane_2_6_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_7_6 plane_2_7_19 543733002463 568649365826 212594706109
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_7_6_sound p h2) (plane_2_7_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_18 plane_1_14_17 plane_2_8_8 92227723283 104793484997 194279197068
      (by decide) p (plane_0_13_18_sound p h0) (plane_1_14_17_sound p h1) (plane_2_8_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_14_14 plane_2_9_8 198540874785 146784996522 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_14_14_sound p h1) (plane_2_9_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_10_12 plane_2_10_18 556142498998 286058466951 28422632345
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_10_12_sound p h2) (plane_2_10_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_11_13 plane_2_11_19 569452994580 286092288567 21090479789
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_0_13_19 plane_2_12_12 58966354913 135560397220 374429679494
      (by decide) p (plane_0_13_14_sound p h0) (plane_0_13_19_sound p h0) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_0_13_19 plane_2_13_13 4966236753 95728368055 187214839747
      (by decide) p (plane_0_13_14_sound p h0) (plane_0_13_19_sound p h0) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_2_14_14 plane_2_14_16 263577935163 238494224500 94234583558
      (by decide) p (plane_0_13_14_sound p h0) (plane_2_14_14_sound p h2) (plane_2_14_16_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_14_14 plane_2_15_17 10571859773 550923098302 282190942442
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_14_14_sound p h1) (plane_2_15_17_sound p h2))

theorem complete_13_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    (e1 : labels 1 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 15 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact complete_13_15_0 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_1_15_15 plane_2_1_9 286092288567 40357234280 248412460584
      (by decide) p (plane_0_13_16_sound p h0) (plane_1_15_15_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_2_4 plane_2_2_10 146561981297 74160944991 2565962934
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_13 plane_1_15_15 plane_2_3_5 65045933361 979437441292 569452994580
      (by decide) p (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1) (plane_2_3_5_sound p h2))
  · exact complete_13_15_4 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_13_16 plane_1_15_14 plane_2_5_4 19219160425 27631156413 16091708513
      (by decide) p (plane_0_13_16_sound p h0) (plane_1_15_14_sound p h1) (plane_2_5_4_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_13 plane_1_15_15 plane_2_6_8 1039080153 55552212773 28472649729
      (by decide) p (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1) (plane_2_6_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_7_6 plane_2_7_19 77676143209 81244543299 30352639179
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_7_6_sound p h2) (plane_2_7_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_1_15_17 plane_2_8_8 6587121193 282585774453 565595488056
      (by decide) p (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1) (plane_2_8_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_17 plane_2_9_4 plane_2_9_9 146593533603 9944130700 269359545447
      (by decide) p (plane_1_15_17_sound p h1) (plane_2_9_4_sound p h2) (plane_2_9_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_17 plane_2_10_10 plane_2_10_12 112810242211 219687422719 3977652280
      (by decide) p (plane_1_15_17_sound p h1) (plane_2_10_10_sound p h2) (plane_2_10_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_11_13 plane_2_11_19 9490883243 4768767144 346360051
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_1_15_17 plane_2_12_12 48098237513 249168225957 565595488056
      (by decide) p (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_17 plane_2_13_13 plane_2_13_16 64367991506 122820427970 753968011
      (by decide) p (plane_1_15_17_sound p h1) (plane_2_13_13_sound p h2) (plane_2_13_16_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_17 plane_2_14_14 plane_2_14_16 527155870326 1039767016309 10571859773
      (by decide) p (plane_1_15_17_sound p h1) (plane_2_14_14_sound p h2) (plane_2_14_16_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_17 plane_2_15_13 plane_2_15_15 142363248645 2565962934 278662161113
      (by decide) p (plane_1_15_17_sound p h1) (plane_2_15_13_sound p h2) (plane_2_15_15_sound p h2))

theorem complete_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 13 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_1_0_6 plane_1_0_8 94265914676 59675557 97720717173
      (by decide) p (plane_0_13_13_sound p h0) (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_1_1_9 plane_1_1_15 19474358512 20153490419 17937121
      (by decide) p (plane_0_13_13_sound p h0) (plane_1_1_9_sound p h1) (plane_1_1_15_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_1_2_10 144976325411 1813877443 146115791345
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_1_2_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_1_3_11 226688241726 29600136713 292231582690
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_1_3_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_1_4_12 273061638778 8417041069 292231582690
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_1_4_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_1_5_14 106627914982 144120846551 146115791345
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_1_5_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_16 plane_1_6_14 126193207060 2669356303 128735983012
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_16_sound p h0) (plane_1_6_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_13_13 plane_0_13_14 plane_1_7_15 273061638778 8417041069 292231582690
      (by decide) p (plane_0_13_13_sound p h0) (plane_0_13_14_sound p h0) (plane_1_7_15_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_8_14 plane_1_8_16 80252589307 37781373621 56395874363
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_8_14_sound p h1) (plane_1_8_16_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_1_9_14 plane_1_9_17 146115791345 144976325411 37885836517
      (by decide) p (plane_0_13_14_sound p h0) (plane_1_9_14_sound p h1) (plane_1_9_17_sound p h1))
  · exact complete_13_10 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_13_12 plane_1_11_14 plane_1_11_19 286122431238 273727962933 121004392604
      (by decide) p (plane_0_13_12_sound p h0) (plane_1_11_14_sound p h1) (plane_1_11_19_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_13_14 plane_0_13_18 plane_1_12_18 121672596446 141436272731 139669658299
      (by decide) p (plane_0_13_14_sound p h0) (plane_0_13_18_sound p h0) (plane_1_12_18_sound p h1))
  · exact complete_13_13 labels p h e0 he
  · exact complete_13_14 labels p h e0 he
  · exact complete_13_15 labels p h e0 he

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_13
