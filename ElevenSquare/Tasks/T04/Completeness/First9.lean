import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 9.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_9_6_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 6)
    (e2 : labels 2 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 2 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_0_9_12 plane_3_0_6 542395821437 19888261400 275073929313
      (by decide) p (plane_0_9_9_sound p h0) (plane_0_9_12_sound p h0) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_8 plane_1_6_15 plane_3_1_9 12950473337 13236058319 25620803478
      (by decide) p (plane_0_9_8_sound p h0) (plane_1_6_15_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_15 plane_2_2_9 plane_3_2_9 20318017992 8154722029 22367449111
      (by decide) p (plane_1_6_15_sound p h1) (plane_2_2_9_sound p h2) (plane_3_2_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_2_2_10 plane_3_3_5 546434044369 49495462403 300648190012
      (by decide) p (plane_1_6_14_sound p h1) (plane_2_2_10_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_2_10 plane_3_4_9 148364852779 43965581069 150282144431
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_2_10_sound p h2) (plane_3_4_9_sound p h3))
  · refine ⟨(127 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row127]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_2_9 plane_3_6_6 plane_3_6_9 146115791345 37885836517 144976325411
      (by decide) p (plane_2_2_9_sound p h2) (plane_3_6_6_sound p h3) (plane_3_6_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_2_2_10 plane_3_7_9 30344966189 587576391 15823588948
      (by decide) p (plane_1_6_14_sound p h1) (plane_2_2_10_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_2_10 plane_3_8_4 8058987727 589503107161 307517547530
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_2_10_sound p h2) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_9_9 157020959 8840126143 9044004372
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_10_10 157020959 8840126143 9044004372
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_2_10 plane_3_11_11 8417041069 292859327197 307517547530
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_2_10_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_2_10 plane_3_12_12 29600136713 257938437109 307517547530
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_2_10_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_2_10 plane_3_13_13 1813877443 153748074324 153758773765
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_2_10_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_14_14 520176509 296584132177 307496148648
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_15_15 59675557 49436485637 51249358108
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_9_6_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 6)
    (e2 : labels 2 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 5 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_5_5 plane_3_0_6 113087766537 3977652280 57998843053
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_5_5_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_8 plane_1_6_15 plane_3_1_9 12950473337 13236058319 25620803478
      (by decide) p (plane_0_9_8_sound p h0) (plane_1_6_15_sound p h1) (plane_3_1_9_sound p h3))
  · refine ⟨(128 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row128]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_1_6_15 plane_3_3_6 36057965052 7487938076 48064530945
      (by decide) p (plane_1_6_14_sound p h1) (plane_1_6_15_sound p h1) (plane_3_3_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_5_13 plane_3_4_9 7707188565 2313977951 7737499067
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_5_13_sound p h2) (plane_3_4_9_sound p h3))
  · refine ⟨(129 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row129]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(130 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row130]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_3_7_9 plane_3_7_19 1104672086663 576194818729 11163951429
      (by decide) p (plane_1_6_14_sound p h1) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_5_13 plane_3_8_13 14694915777 4248202933 15474998134
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_5_13_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_5_10 plane_2_5_13 plane_3_9_10 148796686621 32940028859 144488640871
      (by decide) p (plane_2_5_10_sound p h2) (plane_2_5_13_sound p h2) (plane_3_9_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_5_13 plane_3_10_10 19258425 406781168 407236793
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_5_13_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_3_11_13 plane_3_11_19 94908832430 48337256299 551711303
      (by decide) p (plane_1_6_14_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_5_13 plane_3_12_12 21478273037 257938437109 300564288862
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_5_13_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_5_13 plane_3_13_13 2669356303 153758773765 150324095006
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_5_13_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_5_13 plane_3_14_14 9078349777 296584132177 300648190012
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_5_13_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_5_13 plane_3_15_15 plane_3_15_17 282797744028 286489913177 4460421057
      (by decide) p (plane_2_5_13_sound p h2) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_9_6_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 6)
    (e2 : labels 2 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 6 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_6_6 plane_3_0_6 293162151519 9944130700 150282144431
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_6_6_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_6_6 plane_3_1_9 520176509 296610908583 307517547530
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_6_6_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_6 plane_2_6_9 plane_3_2_9 37885836517 144976325411 146115791345
      (by decide) p (plane_2_6_6_sound p h2) (plane_2_6_9_sound p h2) (plane_3_2_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_2_6_6 plane_3_3_6 3381599606 591153006 3955897237
      (by decide) p (plane_1_6_14_sound p h1) (plane_2_6_6_sound p h2) (plane_3_3_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_3_4_9 plane_3_4_12 285288226896 286480696885 87931162138
      (by decide) p (plane_0_9_9_sound p h0) (plane_3_4_9_sound p h3) (plane_3_4_12_sound p h3))
  · refine ⟨(131 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row131]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(132 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row132]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_3_7_9 plane_3_7_19 1104672086663 576194818729 11163951429
      (by decide) p (plane_1_6_14_sound p h1) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_6_14 plane_3_8_13 14694915777 4248202933 15474998134
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_6_14_sound p h2) (plane_3_8_13_sound p h3))
  · refine ⟨(133 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row133]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_6_13 plane_3_10_10 plane_3_10_13 144488640871 108257512397 94515900045
      (by decide) p (plane_1_6_13_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_3_11_13 plane_3_11_19 94908832430 48337256299 551711303
      (by decide) p (plane_1_6_14_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_6_14 plane_3_12_12 21478273037 257938437109 300564288862
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_6_14_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_6_14 plane_3_13_13 140492437 7911794474 7737499067
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_6_14_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_6_14 plane_3_14_14 9078349777 296584132177 300648190012
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_6_14_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_14 plane_3_15_15 plane_3_15_17 282797744028 286489913177 4460421057
      (by decide) p (plane_2_6_14_sound p h2) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_9_6_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 6)
    (e2 : labels 2 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 9 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_9_9 plane_3_0_8 4460421057 148321889982 150282144431
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_9_9_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_9_9 plane_3_1_9 9078349777 296610908583 300564288862
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_9_9_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_9_9 plane_3_2_10 157020959 9044004372 8840126143
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_9_9_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_9_9 plane_3_3_10 128862563363 174443320480 150282144431
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_9_9_sound p h2) (plane_3_3_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_9_17 plane_3_4_9 148364852779 43965581069 150282144431
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_9_17_sound p h2) (plane_3_4_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_9_10 plane_3_5_10 plane_3_5_13 144488640871 148796686621 32940028859
      (by decide) p (plane_2_9_10_sound p h2) (plane_3_5_10_sound p h3) (plane_3_5_13_sound p h3))
  · refine ⟨(134 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row134]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_2_9_9 plane_3_7_10 14694915777 4938379633 15457684384
      (by decide) p (plane_1_6_14_sound p h1) (plane_2_9_9_sound p h2) (plane_3_7_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_9_17 plane_3_8_13 282973951883 80715855727 300564288862
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_9_17_sound p h2) (plane_3_8_13_sound p h3))
  · refine ⟨(135 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row135]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_6_13 plane_3_10_10 plane_3_10_13 144488640871 108257512397 94515900045
      (by decide) p (plane_1_6_13_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_2_9_17 plane_3_11_13 295155055633 1655133909 150324095006
      (by decide) p (plane_1_6_14_sound p h1) (plane_2_9_17_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_9_17 plane_3_12_17 6763199212 869187012 7909586549
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_9_17_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_6_8 plane_3_13_13 10415553607 153748074324 295155055633
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_6_8_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_9_17 plane_3_14_14 520176509 296584132177 307496148648
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_9_17_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_3_15_15 plane_3_15_17 141398872014 281228124047 5195400765
      (by decide) p (plane_0_9_15_sound p h0) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_9_9_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 9)
    (e2 : labels 2 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 9 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 6 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_3_0_6 plane_3_0_8 282797744028 145011768897 3615241625
      (by decide) p (plane_1_9_9_sound p h1) (plane_3_0_6_sound p h3) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_6_6 plane_3_1_9 520176509 296610908583 307517547530
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_6_6_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_1_9_15 plane_3_2_10 10415553607 150282144431 288682233706
      (by decide) p (plane_1_9_9_sound p h1) (plane_1_9_15_sound p h1) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_15 plane_2_6_8 plane_3_3_6 7752048309 61434141449 141478232315
      (by decide) p (plane_1_9_15_sound p h1) (plane_2_6_8_sound p h2) (plane_3_3_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_3_4_9 plane_3_4_12 285288226896 286171280935 101682896638
      (by decide) p (plane_1_9_9_sound p h1) (plane_3_4_9_sound p h3) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_10 plane_3_5_10 plane_3_5_13 144488640871 94515900045 108257512397
      (by decide) p (plane_1_9_10_sound p h1) (plane_3_5_10_sound p h3) (plane_3_5_13_sound p h3))
  · refine ⟨(136 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row136]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_9_15 plane_2_6_8 plane_3_7_10 31070986843 107818948719 226365171704
      (by decide) p (plane_1_9_15_sound p h1) (plane_2_6_8_sound p h2) (plane_3_7_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_6_14 plane_3_8_13 14694915777 4938379633 15457684384
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_6_14_sound p h2) (plane_3_8_13_sound p h3))
  · refine ⟨(137 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row137]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_6_13 plane_3_10_10 plane_3_10_13 144488640871 32940028859 148796686621
      (by decide) p (plane_2_6_13_sound p h2) (plane_3_10_10_sound p h3) (plane_3_10_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_9 plane_2_6_14 plane_3_11_13 288280977931 117984500434 144488640871
      (by decide) p (plane_2_6_9_sound p h2) (plane_2_6_14_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_6_14 plane_3_12_12 21478273037 258269678195 300648190012
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_6_14_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_6_14 plane_3_13_13 140492437 7911794474 7737499067
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_6_14_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_6_14 plane_3_14_14 477807883 15257327885 15474998134
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_6_14_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_14 plane_3_15_15 plane_3_15_17 282797744028 286489913177 4460421057
      (by decide) p (plane_2_6_14_sound p h2) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_9_9_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 9)
    (e2 : labels 2 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 9 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 9 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_9_9 plane_3_0_8 4460421057 148309456911 150324095006
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_9_9_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_9_9 plane_3_1_9 9078349777 296584132177 300648190012
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_9_9_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_9_9 plane_3_2_10 2669356303 153758773765 150324095006
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_9_9_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_9_9 plane_3_3_10 128862563363 172936668441 150324095006
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_9_9_sound p h2) (plane_3_3_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_9_17 plane_3_4_9 148364852779 50841448319 150324095006
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_9_17_sound p h2) (plane_3_4_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_9_10 plane_3_5_10 plane_3_5_13 144488640871 148796686621 32940028859
      (by decide) p (plane_2_9_10_sound p h2) (plane_3_5_10_sound p h3) (plane_3_5_13_sound p h3))
  · refine ⟨(138 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row138]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_9_9 plane_3_7_10 279203399763 87603658687 300648190012
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_9_9_sound p h2) (plane_3_7_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_9_17 plane_3_8_13 282973951883 93829213027 300648190012
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_9_17_sound p h2) (plane_3_8_13_sound p h3))
  · refine ⟨(139 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row139]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_9_10 plane_0_9_14 plane_3_10_10 3119515037 4609327155 7604665309
      (by decide) p (plane_0_9_10_sound p h0) (plane_0_9_14_sound p h0) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_14 plane_1_9_14 plane_3_11_14 123563208361 159622266029 108904366337
      (by decide) p (plane_0_9_14_sound p h0) (plane_1_9_14_sound p h1) (plane_3_11_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_0_9_17 plane_3_12_12 257938437109 39328026361 590105431712
      (by decide) p (plane_0_9_15_sound p h0) (plane_0_9_17_sound p h0) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_0_9_15 plane_3_13_13 3467060182 75162047503 144341116853
      (by decide) p (plane_0_9_9_sound p h0) (plane_0_9_15_sound p h0) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_9_17 plane_3_14_14 27377711 15257327885 15819173098
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_9_17_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_3_15_15 plane_3_15_17 141398872014 281228124047 5195400765
      (by decide) p (plane_0_9_15_sound p h0) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_9_10_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_9_12 plane_1_10_10 plane_3_1_9 289994215265 84016202474 279203399763
      (by decide) p (plane_0_9_12_sound p h0) (plane_1_10_10_sound p h1) (plane_3_1_9_sound p h3))
  · refine ⟨(140 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row140]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_9_12 plane_0_9_17 plane_3_3_6 41390492312 225578898288 284027168089
      (by decide) p (plane_0_9_12_sound p h0) (plane_0_9_17_sound p h0) (plane_3_3_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_3_4_5 plane_3_4_10 23403467649 100311146 11869003391
      (by decide) p (plane_1_10_10_sound p h1) (plane_3_4_5_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_3_5_6 plane_3_5_10 146115791345 52496582228 97785562203
      (by decide) p (plane_1_10_10_sound p h1) (plane_3_5_6_sound p h3) (plane_3_5_10_sound p h3))
  · refine ⟨(141 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row141]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_9_12 plane_0_9_17 plane_3_7_10 90948203851 235449636515 284027168089
      (by decide) p (plane_0_9_12_sound p h0) (plane_0_9_17_sound p h0) (plane_3_7_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_5_13 plane_3_8_13 14694915777 4938379633 15457684384
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_5_13_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_5_13 plane_3_9_10 7831404559 4974521055 7728842192
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_5_13_sound p h2) (plane_3_9_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_5_13 plane_3_10_10 19258425 407236793 406781168
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_5_13_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_5_13 plane_3_11_11 plane_3_11_13 561792632189 576561955862 234817143
      (by decide) p (plane_2_5_13_sound p h2) (plane_3_11_11_sound p h3) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_5_13 plane_3_12_14 14247734661 6328914549 7728842192
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_5_13_sound p h2) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_5_13 plane_3_13_13 8264261 465269797 454637776
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_5_13_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_5_13 plane_3_14_14 477807883 15262853435 15457684384
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_5_13_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_5_13 plane_3_15_15 plane_3_15_17 282797744028 286489913177 4460421057
      (by decide) p (plane_2_5_13_sound p h2) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_9_10_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 9 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_9_9 plane_3_0_8 4460421057 148321889982 150282144431
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_9_9_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_9_9 plane_3_1_9 9078349777 296610908583 300564288862
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_9_9_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_9_9 plane_3_2_10 157020959 9044004372 8840126143
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_9_9_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_9_9 plane_3_3_11 1130435423 13245405489 15457684384
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_9_9_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_3_4_4 plane_3_4_10 94908832430 551711303 48337256299
      (by decide) p (plane_1_10_10_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_9_9 plane_3_5_10 1866373621 690744503 1932210548
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_9_9_sound p h2) (plane_3_5_10_sound p h3))
  · refine ⟨(142 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row142]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_9_9 plane_3_7_10 279203399763 90948203851 300564288862
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_9_9_sound p h2) (plane_3_7_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_9_17 plane_3_8_13 282973951883 93829213027 300648190012
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_9_17_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_1_10_13 plane_3_9_10 108257512397 94515900045 144488640871
      (by decide) p (plane_1_10_10_sound p h1) (plane_1_10_13_sound p h1) (plane_3_9_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_10_13 plane_3_10_10 26248291114 75162047503 73395101427
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_10_13_sound p h1) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_3_11_10 plane_3_11_14 144193592835 49368533333 100955561673
      (by decide) p (plane_0_9_17_sound p h0) (plane_3_11_10_sound p h3) (plane_3_11_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_9_17 plane_3_12_17 3381599606 591153006 3955897237
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_9_17_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_1_10_10 plane_3_13_13 150282144431 6934120364 288280977931
      (by decide) p (plane_0_9_15_sound p h0) (plane_1_10_10_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_9_17 plane_3_14_14 27377711 15262853435 15823588948
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_9_17_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_3_15_15 plane_3_15_17 141398872014 281228124047 5195400765
      (by decide) p (plane_0_9_15_sound p h0) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_9_11_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 11)
    (e2 : labels 2 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 11 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 5 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_2_5_5 plane_3_0_6 565438832685 18920357693 282557077259
      (by decide) p (plane_1_11_11_sound p h1) (plane_2_5_5_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_8 plane_3_1_6 plane_3_1_9 279339316598 198540874785 204073209213
      (by decide) p (plane_0_9_8_sound p h0) (plane_3_1_6_sound p h3) (plane_3_1_9_sound p h3))
  · refine ⟨(143 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row143]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_5_5 plane_3_3_6 248405159872 41390492312 296584132177
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_5_5_sound p h2) (plane_3_3_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_1_11_13 plane_3_4_9 565149005286 85908869290 561792632189
      (by decide) p (plane_1_11_11_sound p h1) (plane_1_11_13_sound p h1) (plane_3_4_9_sound p h3))
  · refine ⟨(144 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row144]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_11_10 plane_1_11_14 plane_3_6_6 47614852103 102667292328 144193592835
      (by decide) p (plane_1_11_10_sound p h1) (plane_1_11_14_sound p h1) (plane_3_6_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_12 plane_1_11_14 plane_3_7_10 302248561216 235449636515 175725312954
      (by decide) p (plane_0_9_12_sound p h0) (plane_1_11_14_sound p h1) (plane_3_7_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_1_11_13 plane_3_8_13 539094743595 78867780424 561792632189
      (by decide) p (plane_1_11_11_sound p h1) (plane_1_11_13_sound p h1) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_10 plane_3_9_9 48085516977 75162047503 72847748238
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_10_sound p h1) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_3_10_10 1655133909 150324095006 295155055633
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_3_11_11 29364529509 292859327197 590310111266
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_3_12_12 68452719217 257938437109 590310111266
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_3_13_13 10415553607 153748074324 295155055633
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_3_14_14 12377849851 296610908583 590310111266
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_3_15_15 6345271797 148321889982 295155055633
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_9_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_9_12 plane_1_6_14 plane_2_0_6 1046750600 28349296573 14694915777
      (by decide) p (plane_0_9_12_sound p h0) (plane_1_6_14_sound p h1) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_6_15 plane_2_1_6 plane_2_1_9 279339316598 198540874785 204073209213
      (by decide) p (plane_1_6_15_sound p h1) (plane_2_1_6_sound p h2) (plane_2_1_9_sound p h2))
  · exact complete_9_6_2 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_0_9_12 plane_2_3_6 82910326544 14975876152 91691309771
      (by decide) p (plane_0_9_9_sound p h0) (plane_0_9_12_sound p h0) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_2_4_4 plane_2_4_10 47454416215 2550867439 24160503512
      (by decide) p (plane_1_6_14_sound p h1) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact complete_9_6_5 labels p h e0 e1 he
  · exact complete_9_6_6 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_2_7_6 plane_2_7_10 284027168089 93829213027 206735075835
      (by decide) p (plane_0_9_9_sound p h0) (plane_2_7_6_sound p h2) (plane_2_7_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_2_8_8 plane_2_8_14 548479375832 37825715679 286480696885
      (by decide) p (plane_1_6_14_sound p h1) (plane_2_8_8_sound p h2) (plane_2_8_14_sound p h2))
  · exact complete_9_6_9 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_9_10 plane_1_6_14 plane_2_10_10 7728842192 4974521055 7831404559
      (by decide) p (plane_0_9_10_sound p h0) (plane_1_6_14_sound p h1) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_1_6_8 plane_2_11_10 272741144013 96171033954 288280977931
      (by decide) p (plane_0_9_9_sound p h0) (plane_1_6_8_sound p h1) (plane_2_11_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_1_6_8 plane_2_12_12 39328026361 251662704291 576561955862
      (by decide) p (plane_0_9_9_sound p h0) (plane_1_6_8_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_10 plane_1_6_14 plane_2_13_13 150324095006 92251738721 148796686621
      (by decide) p (plane_0_9_10_sound p h0) (plane_1_6_14_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_6_8 plane_2_14_14 21090479789 296584132177 590310111266
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_6_8_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_6_8 plane_2_15_15 10390801530 148309456911 295155055633
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_6_8_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_9_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 9 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_9_15 plane_2_0_6 plane_2_0_8 141398872014 5195400765 281228124047
      (by decide) p (plane_1_9_15_sound p h1) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_1_9_15 plane_2_1_9 21090479789 289889229815 577364467412
      (by decide) p (plane_1_9_9_sound p h1) (plane_1_9_15_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_1_9_15 plane_2_2_10 3467060182 75162047503 144341116853
      (by decide) p (plane_1_9_9_sound p h1) (plane_1_9_15_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_1_9_15 plane_2_3_6 123993113122 8257276614 144341116853
      (by decide) p (plane_1_9_9_sound p h1) (plane_1_9_15_sound p h1) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_9_14 plane_2_4_13 16725246721 17111215388 24465033809
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_9_14_sound p h1) (plane_2_4_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_9_10 plane_1_9_14 plane_2_5_13 3119515037 4609327155 7604665309
      (by decide) p (plane_1_9_10_sound p h1) (plane_1_9_14_sound p h1) (plane_2_5_13_sound p h2))
  · exact complete_9_9_6 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_7_6 plane_2_7_10 284027168089 80715855727 219932334285
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_7_6_sound p h2) (plane_2_7_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_0_9_17 plane_2_8_13 87603658687 539094743595 590105431712
      (by decide) p (plane_0_9_15_sound p h0) (plane_0_9_17_sound p h0) (plane_2_8_13_sound p h2))
  · exact complete_9_9_9 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_9_10 plane_2_10_10 plane_2_10_13 144488640871 108257512397 94515900045
      (by decide) p (plane_0_9_10_sound p h0) (plane_2_10_10_sound p h2) (plane_2_10_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_1_9_9 plane_2_11_10 102882420579 284229636552 288280977931
      (by decide) p (plane_0_9_15_sound p h0) (plane_1_9_9_sound p h1) (plane_2_11_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_1_9_9 plane_2_12_12 252961440741 68452719217 576561955862
      (by decide) p (plane_0_9_15_sound p h0) (plane_1_9_9_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_0_9_15 plane_2_13_13 10415553607 150282144431 288682233706
      (by decide) p (plane_0_9_9_sound p h0) (plane_0_9_15_sound p h0) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_0_9_15 plane_2_14_14 12377849851 289994215265 577364467412
      (by decide) p (plane_0_9_9_sound p h0) (plane_0_9_15_sound p h0) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_0_9_15 plane_2_15_15 6345271797 145011768897 288682233706
      (by decide) p (plane_0_9_9_sound p h0) (plane_0_9_15_sound p h0) (plane_2_15_15_sound p h2))

theorem complete_9_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_9_12 plane_0_9_17 plane_2_0_9 28769887088 30598113403 40575309727
      (by decide) p (plane_0_9_12_sound p h0) (plane_0_9_17_sound p h0) (plane_2_0_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_12 plane_1_10_10 plane_2_1_9 289889229815 88201229486 279203399763
      (by decide) p (plane_0_9_12_sound p h0) (plane_1_10_10_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_1_10_15 plane_2_2_9 12250414744 10117034367 16021510315
      (by decide) p (plane_1_10_10_sound p h1) (plane_1_10_15_sound p h1) (plane_2_2_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_12 plane_1_10_10 plane_2_3_6 11009702152 82910326544 93067799921
      (by decide) p (plane_0_9_12_sound p h0) (plane_1_10_10_sound p h1) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_2_4_9 plane_2_4_13 144193592835 102667292328 47614852103
      (by decide) p (plane_0_9_17_sound p h0) (plane_2_4_9_sound p h2) (plane_2_4_13_sound p h2))
  · exact complete_9_10_5 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_1_10_13 plane_2_6_9 118244314584 59270785703 144488640871
      (by decide) p (plane_1_10_10_sound p h1) (plane_1_10_13_sound p h1) (plane_2_6_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_7_6 plane_2_7_15 53402669690 57296139377 43986466857
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_7_6_sound p h2) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_0_9_17 plane_2_8_13 87603658687 539094743595 590105431712
      (by decide) p (plane_0_9_15_sound p h0) (plane_0_9_17_sound p h0) (plane_2_8_13_sound p h2))
  · exact complete_9_10_9 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_1_10_10 plane_2_10_13 59270785703 284317302986 288280977931
      (by decide) p (plane_0_9_15_sound p h0) (plane_1_10_10_sound p h1) (plane_2_10_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_11_13 plane_2_11_19 47454416215 24160503512 2550867439
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_1_10_10 plane_2_12_12 252961440741 68452719217 576561955862
      (by decide) p (plane_0_9_15_sound p h0) (plane_1_10_10_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_10 plane_0_9_17 plane_2_13_13 153758773765 92251738721 150558320767
      (by decide) p (plane_0_9_10_sound p h0) (plane_0_9_17_sound p h0) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_1_10_10 plane_2_14_14 289889229815 12377849851 576561955862
      (by decide) p (plane_0_9_15_sound p h0) (plane_1_10_10_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_1_10_10 plane_2_15_17 9944130700 562821523819 288280977931
      (by decide) p (plane_0_9_15_sound p h0) (plane_1_10_10_sound p h1) (plane_2_15_17_sound p h2))

theorem complete_9_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    (e1 : labels 1 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 11 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_9_12 plane_0_9_17 plane_2_0_9 28769887088 30598113403 40575309727
      (by decide) p (plane_0_9_12_sound p h0) (plane_0_9_17_sound p h0) (plane_2_0_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_12 plane_1_11_11 plane_2_1_9 282557077259 88201229486 268090853421
      (by decide) p (plane_0_9_12_sound p h0) (plane_1_11_11_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_8 plane_1_11_10 plane_2_2_9 22367449111 8154722029 21350669565
      (by decide) p (plane_0_9_8_sound p h0) (plane_1_11_10_sound p h1) (plane_2_2_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_12 plane_1_11_11 plane_2_3_6 14524919400 82910326544 89363617807
      (by decide) p (plane_0_9_12_sound p h0) (plane_1_11_11_sound p h1) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_2_4_9 288046348647 47614852103 295155055633
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_2_4_9_sound p h2))
  · exact complete_9_11_5 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_11_10 plane_2_6_6 plane_2_6_9 146115791345 100351480326 100955561673
      (by decide) p (plane_1_11_10_sound p h1) (plane_2_6_6_sound p h2) (plane_2_6_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_1_11_13 plane_2_7_6 535300478849 201657322281 561792632189
      (by decide) p (plane_1_11_11_sound p h1) (plane_1_11_13_sound p h1) (plane_2_7_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_2_8_8 3686431551 292938243343 590310111266
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_2_8_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_10 plane_2_9_9 102882420579 150282144431 145695496476
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_10_sound p h1) (plane_2_9_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_2_10_10 15305204634 150282144431 295155055633
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_1_11_13 plane_2_11_10 545482288026 187637155215 561792632189
      (by decide) p (plane_1_11_11_sound p h1) (plane_1_11_13_sound p h1) (plane_2_11_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_1_11_13 plane_2_12_12 39328026361 245232080481 561792632189
      (by decide) p (plane_1_11_11_sound p h1) (plane_1_11_13_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_2_13_13 6934120364 153758773765 295155055633
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_2_14_14 21090479789 296584132177 590310111266
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_11_13 plane_2_15_15 10390801530 148309456911 295155055633
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_11_13_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 9 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_1_0_6 plane_1_0_8 282797744028 4460421057 286489913177
      (by decide) p (plane_0_9_9_sound p h0) (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_1_1_9 plane_1_1_15 80679485264 79082717605 1296907111
      (by decide) p (plane_0_9_9_sound p h0) (plane_1_1_9_sound p h1) (plane_1_1_15_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_1_2_10 plane_1_2_11 284027168089 273864687157 5338712606
      (by decide) p (plane_0_9_9_sound p h0) (plane_1_2_10_sound p h1) (plane_1_2_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_9_9 plane_0_9_15 plane_1_3_11 496971563523 21478273037 577364467412
      (by decide) p (plane_0_9_9_sound p h0) (plane_0_9_15_sound p h0) (plane_1_3_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_9_10 plane_1_4_10 plane_1_4_12 561792632189 281713496990 340592954994
      (by decide) p (plane_0_9_10_sound p h0) (plane_1_4_10_sound p h1) (plane_1_4_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_9_10 plane_1_5_10 plane_1_5_13 144488640871 148796686621 32940028859
      (by decide) p (plane_0_9_10_sound p h0) (plane_1_5_10_sound p h1) (plane_1_5_13_sound p h1))
  · exact complete_9_6 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_9_8 plane_1_7_10 plane_1_7_15 30219441171 31203773929 11497565201
      (by decide) p (plane_0_9_8_sound p h0) (plane_1_7_10_sound p h1) (plane_1_7_15_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_0_9_17 plane_1_8_13 282973951883 155354934215 590105431712
      (by decide) p (plane_0_9_15_sound p h0) (plane_0_9_17_sound p h0) (plane_1_8_13_sound p h1))
  · exact complete_9_9 labels p h e0 he
  · exact complete_9_10 labels p h e0 he
  · exact complete_9_11 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_12_12 plane_1_12_18 452528907170 546434044369 29600136713
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_12_12_sound p h1) (plane_1_12_18_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_9_14 plane_0_9_17 plane_1_13_14 144976325411 37885836517 146115791345
      (by decide) p (plane_0_9_14_sound p h0) (plane_0_9_17_sound p h0) (plane_1_13_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_9_15 plane_0_9_17 plane_1_14_14 520176509 569141090689 590105431712
      (by decide) p (plane_0_9_15_sound p h0) (plane_0_9_17_sound p h0) (plane_1_14_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_9_17 plane_1_15_13 plane_1_15_15 284726497290 179026671 294976028962
      (by decide) p (plane_0_9_17_sound p h0) (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_9
