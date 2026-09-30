import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 4.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_4_6_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    (e1 : labels 1 = 6)
    (e2 : labels 2 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 2 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_1_6_11 plane_3_0_9 214186793821 348363738638 175725312954
      (by decide) p (plane_0_4_9_sound p h0) (plane_1_6_11_sound p h1) (plane_3_0_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_11 plane_1_6_15 plane_3_1_9 194257100055 88201229486 271974970539
      (by decide) p (plane_1_6_11_sound p h1) (plane_1_6_15_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_15 plane_2_2_9 plane_3_2_9 20318017992 8154722029 22367449111
      (by decide) p (plane_1_6_15_sound p h1) (plane_2_2_9_sound p h2) (plane_3_2_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_2_2_10 plane_3_3_5 546434044369 48652965083 292938243343
      (by decide) p (plane_0_4_12_sound p h0) (plane_2_2_10_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_4_9 11412680983 3662680931 11826774948
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_4_9_sound p h3))
  · refine ⟨(40 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row40]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_4_13 plane_3_6_6 plane_3_6_9 146115791345 100351480326 100955561673
      (by decide) p (plane_0_4_13_sound p h0) (plane_3_6_6_sound p h3) (plane_3_6_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_2_2_10 plane_3_7_9 576554357591 11327968305 292938243343
      (by decide) p (plane_0_4_12_sound p h0) (plane_2_2_10_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_2_10 plane_3_8_4 plane_3_8_6 1123889340121 578265315311 8058987727
      (by decide) p (plane_2_2_10_sound p h2) (plane_3_8_4_sound p h3) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_9_9 157020959 8840126143 9044004372
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_10_10 157020959 8840126143 9044004372
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_2_2_10 plane_3_11_11 8417041069 278839160131 292938243343
      (by decide) p (plane_0_4_12_sound p h0) (plane_2_2_10_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_2_2_10 plane_3_12_12 29600136713 245232080481 292938243343
      (by decide) p (plane_0_4_12_sound p h0) (plane_2_2_10_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_2_10 plane_3_13_13 plane_3_13_14 146115791345 144976325411 1813877443
      (by decide) p (plane_2_2_10_sound p h2) (plane_3_13_13_sound p h3) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_14_14 520176509 296584132177 307496148648
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_2_10 plane_3_15_15 59675557 49436485637 51249358108
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_2_10_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_4_6_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    (e1 : labels 1 = 6)
    (e2 : labels 2 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 5 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_2_5_5 plane_2_5_11 plane_3_0_9 20962324321 14907783697 29270657842
      (by decide) p (plane_2_5_5_sound p h2) (plane_2_5_11_sound p h2) (plane_3_0_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_15 plane_2_5_6 plane_3_1_9 282190942442 194257100055 402614083998
      (by decide) p (plane_1_6_15_sound p h1) (plane_2_5_6_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_13 plane_1_6_15 plane_3_2_9 8154722029 22367449111 21350669565
      (by decide) p (plane_0_4_13_sound p h0) (plane_1_6_15_sound p h1) (plane_3_2_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_0_4_12 plane_3_3_5 48652965083 1044483374653 561792632189
      (by decide) p (plane_0_4_10_sound p h0) (plane_0_4_12_sound p h0) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_5_10 plane_3_4_4 plane_3_4_9 143061215619 9080134097 140881595292
      (by decide) p (plane_2_5_10_sound p h2) (plane_3_4_4_sound p h3) (plane_3_4_9_sound p h3))
  · refine ⟨(41 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row41]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_4_13 plane_3_6_6 plane_3_6_9 146115791345 100351480326 100955561673
      (by decide) p (plane_0_4_13_sound p h0) (plane_3_6_6_sound p h3) (plane_3_6_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_3_7_9 plane_3_7_19 1104672086663 561424934584 11327968305
      (by decide) p (plane_0_4_12_sound p h0) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_0_4_12 plane_3_8_8 278839160131 98843541670 285288226896
      (by decide) p (plane_0_4_9_sound p h0) (plane_0_4_12_sound p h0) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_0_4_12 plane_3_9_9 286480696885 87931162138 285288226896
      (by decide) p (plane_0_4_9_sound p h0) (plane_0_4_12_sound p h0) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_6_6 plane_3_10_10 150282144431 15305204634 295155055633
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_6_6_sound p h1) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_3_11_11 plane_3_11_13 561792632189 1131825858520 3686431551
      (by decide) p (plane_0_4_10_sound p h0) (plane_3_11_11_sound p h3) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_0_4_12 plane_3_12_12 245232080481 39328026361 561792632189
      (by decide) p (plane_0_4_10_sound p h0) (plane_0_4_12_sound p h0) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_6_6 plane_3_13_13 153758773765 6934120364 295155055633
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_6_6_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_5 plane_0_4_10 plane_3_14_14 21090479789 377406821981 772314432417
      (by decide) p (plane_0_4_5_sound p h0) (plane_0_4_10_sound p h0) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_3_15_15 plane_3_15_17 141398872014 281228124047 5195400765
      (by decide) p (plane_0_4_10_sound p h0) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_4_7_1 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    (e1 : labels 1 = 7)
    (e2 : labels 2 = 1)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 1 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_2_1_7 plane_2_1_9 plane_3_0_5 287626254203 110684373445 527155870326
      (by decide) p (plane_2_1_7_sound p h2) (plane_2_1_9_sound p h2) (plane_3_0_5_sound p h3))
  · refine ⟨(42 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row42]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_2_1_6 plane_3_2_5 194279197068 104793484997 92227723283
      (by decide) p (plane_1_7_15_sound p h1) (plane_2_1_6_sound p h2) (plane_3_2_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_2_1_9 plane_3_3_5 526217738354 72410295677 282557077259
      (by decide) p (plane_1_7_15_sound p h1) (plane_2_1_9_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_4_4 1407478171 95375342880 95374467851
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_4_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_2_1_6 plane_3_5_5 277812578482 282458329541 92227723283
      (by decide) p (plane_1_7_15_sound p h1) (plane_2_1_6_sound p h2) (plane_3_5_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_6_6 520176509 296643779964 286123403553
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_6_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_2_1_9 plane_3_7_9 555772606402 36405618375 282557077259
      (by decide) p (plane_1_7_15_sound p h1) (plane_2_1_9_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_1_9 plane_3_8_4 67699997 1130273258965 568649365826
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_1_9_sound p h2) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_9_9 9078349777 289926042144 286123403553
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_10_10 9078349777 289926042144 286123403553
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_1_9 plane_3_11_11 2145067255 280812131798 284324682913
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_1_9_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_1_9 plane_3_12_12 12588252044 247618483065 284324682913
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_1_9_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_13_13 520176509 296643779964 286123403553
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_14_14 4378363960 286092288567 286123403553
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_15_15 1407478171 95375342880 95374467851
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_4_7_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    (e1 : labels 1 = 7)
    (e2 : labels 2 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 2 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(43 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row43]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(44 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row44]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_3_2_5 plane_3_2_9 279339316598 177664844544 104793484997
      (by decide) p (plane_1_7_15_sound p h1) (plane_3_2_5_sound p h3) (plane_3_2_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_2_2_10 plane_3_3_5 546434044369 72410295677 292859327197
      (by decide) p (plane_1_7_15_sound p h1) (plane_2_2_10_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_3_4_4 plane_3_4_9 6220052853 5583655766 1989468987
      (by decide) p (plane_0_4_9_sound p h0) (plane_3_4_4_sound p h3) (plane_3_4_9_sound p h3))
  · refine ⟨(45 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row45]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_2_2_10 plane_3_6_9 293580405708 115273398799 292859327197
      (by decide) p (plane_1_7_15_sound p h1) (plane_2_2_10_sound p h2) (plane_3_6_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_2_2_10 plane_3_7_9 576554357591 36405618375 292859327197
      (by decide) p (plane_1_7_15_sound p h1) (plane_2_2_10_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_2_10 plane_3_8_4 8058987727 1130273258965 589503107161
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_2_10 plane_3_9_9 2669356303 144963021072 148309456911
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_2_10_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_2_10 plane_3_10_10 2669356303 144963021072 148309456911
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_2_10_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_2_10 plane_3_11_11 8417041069 561624263596 589503107161
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_2_10 plane_3_12_12 29600136713 495236966130 589503107161
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_19 plane_2_2_10 plane_3_13_13 3627754886 589557157165 589503107161
      (by decide) p (plane_1_7_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_2_10 plane_3_14_14 520176509 286092288567 296618913822
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_2_10_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_2_10 plane_3_15_15 59675557 47687671440 49436485637
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_2_10_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_4_7_3 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    (e1 : labels 1 = 7)
    (e2 : labels 2 = 3)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 3 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_3_6 plane_3_0_5 39890497256 30493944443 13408722488
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_3_6_sound p h2) (plane_3_0_5_sound p h3))
  · refine ⟨(46 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row46]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_3_5 plane_3_2_5 plane_3_2_10 288212352061 546434044369 243345192892
      (by decide) p (plane_2_3_5_sound p h2) (plane_3_2_5_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_7_15 plane_3_3_5 72410295677 1044483374653 562547462351
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_7_15_sound p h1) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_3_4_4 plane_3_4_9 6220052853 5583655766 1989468987
      (by decide) p (plane_0_4_9_sound p h0) (plane_3_4_4_sound p h3) (plane_3_4_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_3_6 plane_3_5_5 248405159872 286092288567 40226167464
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_3_6_sound p h2) (plane_3_5_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_2_3_6 plane_3_6_9 28831203004 277866580613 245736565796
      (by decide) p (plane_0_4_10_sound p h0) (plane_2_3_6_sound p h2) (plane_3_6_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_3_7_9 plane_3_7_19 1104672086663 561624263596 36405618375
      (by decide) p (plane_1_7_15_sound p h1) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_1_7_19 plane_3_8_8 280812131798 49421770835 284260371363
      (by decide) p (plane_0_4_9_sound p h0) (plane_1_7_19_sound p h1) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_1_7_19 plane_3_9_9 30326043091 4627955902 29922144354
      (by decide) p (plane_0_4_9_sound p h0) (plane_1_7_19_sound p h1) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_0_4_10 plane_3_10_10 2550867439 24160503512 47454416215
      (by decide) p (plane_0_4_4_sound p h0) (plane_0_4_10_sound p h0) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_3_11_13 plane_3_11_19 189817664860 94164690509 9788176503
      (by decide) p (plane_1_7_15_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_7_19 plane_3_12_12 495236966130 39328026361 1131762613157
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_7_19_sound p h1) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_0_4_10 plane_3_13_13 3467060182 74160944991 142363248645
      (by decide) p (plane_0_4_4_sound p h0) (plane_0_4_10_sound p h0) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_5 plane_0_4_10 plane_3_14_14 21090479789 377406821981 772314432417
      (by decide) p (plane_0_4_5_sound p h0) (plane_0_4_10_sound p h0) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_3_15_15 plane_3_15_17 141398872014 281228124047 5195400765
      (by decide) p (plane_0_4_10_sound p h0) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_4_11_1 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    (e1 : labels 1 = 11)
    (e2 : labels 2 = 1)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 11 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 1 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_4_0 plane_1_11_11 plane_3_0_6 75681430772000000 1057261 528190
      (by decide) p (plane_0_4_0_sound p h0) (plane_1_11_11_sound p h1) (plane_3_0_6_sound p h3))
  · refine ⟨(47 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row47]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(48 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row48]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_2_1_9 plane_3_3_5 526217738354 48652965083 282458329541
      (by decide) p (plane_0_4_12_sound p h0) (plane_2_1_9_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_2_1_9 plane_3_4_4 4222434513 282494071527 282557077259
      (by decide) p (plane_1_11_11_sound p h1) (plane_2_1_9_sound p h2) (plane_3_4_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_1_6 plane_2_1_9 plane_3_5_6 141095471221 41766690707 139669658299
      (by decide) p (plane_2_1_6_sound p h2) (plane_2_1_9_sound p h2) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_2_1_9 plane_3_6_6 520176509 292938243343 282557077259
      (by decide) p (plane_1_11_11_sound p h1) (plane_2_1_9_sound p h2) (plane_3_6_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_1_9 plane_3_7_7 25176504088 248783313891 286092288567
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_1_9_sound p h2) (plane_3_7_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_1_9 plane_3_8_4 67699997 568648995369 286092288567
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_1_9_sound p h2) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_9_9 9078349777 289926042144 286123403553
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_10_10 9078349777 289926042144 286123403553
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_1_9 plane_3_11_11 4290134510 282494071527 286092288567
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_1_9_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_1_9 plane_3_12_12 25176504088 248783313891 286092288567
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_1_9_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_13_13 520176509 296643779964 286123403553
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_14_14 4378363960 286092288567 286123403553
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_1_9 plane_3_15_15 1407478171 95375342880 95374467851
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_1_9_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_4_11_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    (e1 : labels 1 = 11)
    (e2 : labels 2 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 11 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 2 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_4_0 plane_1_11_11 plane_3_0_6 75681430772000000 1057261 528190
      (by decide) p (plane_0_4_0_sound p h0) (plane_1_11_11_sound p h1) (plane_3_0_6_sound p h3))
  · refine ⟨(49 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row49]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(50 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row50]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_2_2_10 plane_3_3_5 546434044369 48652965083 292938243343
      (by decide) p (plane_0_4_12_sound p h0) (plane_2_2_10_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_2_2_10 plane_3_4_9 296729705558 85908869290 292859327197
      (by decide) p (plane_1_11_11_sound p h1) (plane_2_2_10_sound p h2) (plane_3_4_9_sound p h3))
  · refine ⟨(51 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row51]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_1_11_10 plane_3_6_6 205334584656 292859327197 280833965361
      (by decide) p (plane_0_4_12_sound p h0) (plane_1_11_10_sound p h1) (plane_3_6_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_2_2_10 plane_3_7_9 576554357591 11327968305 292938243343
      (by decide) p (plane_0_4_12_sound p h0) (plane_2_2_10_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_2_10 plane_3_8_4 1151283961 81235570767 42377682852
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_8_4_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_2_10 plane_3_9_9 2669356303 144963021072 148309456911
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_2_10_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_2_10 plane_3_10_10 2669356303 144963021072 148309456911
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_2_10_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_2_10 plane_3_11_11 8417041069 282494071527 296643779964
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_2_10 plane_3_12_12 4228590959 35540473413 42377682852
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_19 plane_2_2_10 plane_3_13_13 259125349 21187065273 21188841426
      (by decide) p (plane_1_11_19_sound p h1) (plane_2_2_10_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_2_10 plane_3_14_14 520176509 286092288567 296618913822
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_2_10_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_2_2_10 plane_3_15_15 59675557 47687671440 49436485637
      (by decide) p (plane_0_4_4_sound p h0) (plane_2_2_10_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_4_11_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    (e1 : labels 1 = 11)
    (e2 : labels 2 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_2_5_6 plane_3_1_6 plane_3_1_9 139669658299 141095471221 41766690707
      (by decide) p (plane_2_5_6_sound p h2) (plane_3_1_6_sound p h3) (plane_3_1_9_sound p h3))
  · refine ⟨(52 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row52]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_2_5_5 plane_3_3_6 248405159872 43574758200 282458329541
      (by decide) p (plane_0_4_12_sound p h0) (plane_2_5_5_sound p h2) (plane_3_3_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_1_11_13 plane_3_4_9 565149005286 85908869290 561792632189
      (by decide) p (plane_1_11_11_sound p h1) (plane_1_11_13_sound p h1) (plane_3_4_9_sound p h3))
  · refine ⟨(53 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row53]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_1_11_10 plane_3_6_6 205334584656 292859327197 280833965361
      (by decide) p (plane_0_4_12_sound p h0) (plane_1_11_10_sound p h1) (plane_3_6_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_3_7_9 plane_3_7_19 1104672086663 561424934584 11327968305
      (by decide) p (plane_0_4_12_sound p h0) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_1_11_13 plane_3_8_13 539094743595 78867780424 561792632189
      (by decide) p (plane_1_11_11_sound p h1) (plane_1_11_13_sound p h1) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_1_11_10 plane_3_9_9 10123266732 15077931415 14780735019
      (by decide) p (plane_0_4_12_sound p h0) (plane_1_11_10_sound p h1) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_11_10 plane_1_11_19 plane_3_10_10 48337256299 32057011318 46887091617
      (by decide) p (plane_1_11_10_sound p h1) (plane_1_11_19_sound p h1) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_3_11_11 plane_3_11_13 561792632189 1131825858520 3686431551
      (by decide) p (plane_0_4_10_sound p h0) (plane_3_11_11_sound p h3) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_11_19 plane_3_12_12 248783313891 39328026361 569215150806
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_11_19_sound p h1) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_11_5 plane_3_13_13 617979528253 13868240728 1212302619693
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_11_5_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_11_5 plane_3_14_14 588464037365 21090479789 1212302619693
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_11_5_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_11_5 plane_3_15_15 196279161647 6927201020 404100873231
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_11_5_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_4_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    (e1 : labels 1 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_6_15 plane_2_0_6 plane_2_0_8 94265914676 33068411457 91497157105
      (by decide) p (plane_1_6_15_sound p h1) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_1_6_11 plane_2_1_9 84016202474 282458329541 268090853421
      (by decide) p (plane_0_4_12_sound p h0) (plane_1_6_11_sound p h1) (plane_2_1_9_sound p h2))
  · exact complete_4_6_2 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_6_11 plane_2_3_6 plane_2_3_11 36591812992 16803157013 37596483048
      (by decide) p (plane_1_6_11_sound p h1) (plane_2_3_6_sound p h2) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_2_4_4 plane_2_4_10 189817664860 9788176503 94164690509
      (by decide) p (plane_0_4_12_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact complete_4_6_5 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_2_6_6 plane_2_6_9 146115791345 123563208361 47614852103
      (by decide) p (plane_0_4_9_sound p h0) (plane_2_6_6_sound p h2) (plane_2_6_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_1_6_6 plane_2_7_6 216547944797 207018857010 296729705558
      (by decide) p (plane_0_4_9_sound p h0) (plane_1_6_6_sound p h1) (plane_2_7_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_2_8_8 plane_2_8_14 548479375832 1107729349567 29364529509
      (by decide) p (plane_0_4_10_sound p h0) (plane_2_8_8_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_0_4_12 plane_2_9_9 286171280935 101682896638 285288226896
      (by decide) p (plane_0_4_9_sound p h0) (plane_0_4_12_sound p h0) (plane_2_9_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_5 plane_0_4_10 plane_2_10_10 100311146 11869003391 23403467649
      (by decide) p (plane_0_4_5_sound p h0) (plane_0_4_10_sound p h0) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_2_11_11 plane_2_11_13 561792632189 565149005286 85908869290
      (by decide) p (plane_0_4_9_sound p h0) (plane_2_11_11_sound p h2) (plane_2_11_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_6_6 plane_2_12_12 257938437109 68452719217 590310111266
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_6_6_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_5 plane_0_4_10 plane_2_13_13 20831107214 391813836383 772314432417
      (by decide) p (plane_0_4_5_sound p h0) (plane_0_4_10_sound p h0) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_5 plane_0_4_10 plane_2_14_14 12377849851 381829087459 772314432417
      (by decide) p (plane_0_4_5_sound p h0) (plane_0_4_10_sound p h0) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_6_6 plane_2_15_15 148321889982 6345271797 295155055633
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_6_6_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_4_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    (e1 : labels 1 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 7 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_2_0_6 plane_2_0_8 565595488056 282585774453 6587121193
      (by decide) p (plane_1_7_15_sound p h1) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact complete_4_7_1 labels p h e0 e1 he
  · exact complete_4_7_2 labels p h e0 e1 he
  · exact complete_4_7_3 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_2_4_4 plane_2_4_10 189817664860 1228810517 94195258151
      (by decide) p (plane_1_7_15_sound p h1) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_7_10 plane_1_7_15 plane_2_5_6 63443117992 70761576674 90658323513
      (by decide) p (plane_1_7_10_sound p h1) (plane_1_7_15_sound p h1) (plane_2_5_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_1_7_10 plane_2_6_6 90948203851 95229704206 175725312954
      (by decide) p (plane_0_4_9_sound p h0) (plane_1_7_10_sound p h1) (plane_2_6_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_0_4_9 plane_2_7_6 9858040810 9931292687 13624877678
      (by decide) p (plane_0_4_4_sound p h0) (plane_0_4_9_sound p h0) (plane_2_7_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_7_15 plane_2_8_4 plane_2_8_14 1104672086663 11327968305 561424934584
      (by decide) p (plane_1_7_15_sound p h1) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_1_7_19 plane_2_9_9 30337196791 5351731402 29922144354
      (by decide) p (plane_0_4_9_sound p h0) (plane_1_7_19_sound p h1) (plane_2_9_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_5 plane_0_4_10 plane_2_10_10 100311146 11869003391 23403467649
      (by decide) p (plane_0_4_5_sound p h0) (plane_0_4_10_sound p h0) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_1_7_19 plane_2_11_11 280712467292 42954434645 284260371363
      (by decide) p (plane_0_4_9_sound p h0) (plane_1_7_19_sound p h1) (plane_2_11_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_0_4_10 plane_2_12_12 68452719217 248783313891 569452994580
      (by decide) p (plane_0_4_4_sound p h0) (plane_0_4_10_sound p h0) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_5 plane_0_4_10 plane_2_13_13 20831107214 391813836383 772314432417
      (by decide) p (plane_0_4_5_sound p h0) (plane_0_4_10_sound p h0) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_5 plane_0_4_10 plane_2_14_14 12377849851 381829087459 772314432417
      (by decide) p (plane_0_4_5_sound p h0) (plane_0_4_10_sound p h0) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_0_4_10 plane_2_15_15 2115090599 47692487307 94908832430
      (by decide) p (plane_0_4_4_sound p h0) (plane_0_4_10_sound p h0) (plane_2_15_15_sound p h2))

theorem complete_4_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    (e1 : labels 1 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 11 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_4_0 plane_0_4_12 plane_2_0_6 75681430772000000 1057261 528190
      (by decide) p (plane_0_4_0_sound p h0) (plane_0_4_12_sound p h0) (plane_2_0_6_sound p h2))
  · exact complete_4_11_1 labels p h e0 e1 he
  · exact complete_4_11_2 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_4_0 plane_1_11_11 plane_2_3_6 17429903280000000 46388 52819
      (by decide) p (plane_0_4_0_sound p h0) (plane_1_11_11_sound p h1) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_2_4_4 plane_2_4_10 189817664860 9788176503 94164690509
      (by decide) p (plane_0_4_12_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact complete_4_11_5 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_1_11_10 plane_2_6_6 201911123346 292938243343 280833965361
      (by decide) p (plane_0_4_12_sound p h0) (plane_1_11_10_sound p h1) (plane_2_6_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_11 plane_1_11_13 plane_2_7_6 535300478849 201657322281 561792632189
      (by decide) p (plane_1_11_11_sound p h1) (plane_1_11_13_sound p h1) (plane_2_7_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_13 plane_1_11_19 plane_2_8_8 94195258151 1228810517 189817664860
      (by decide) p (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1) (plane_2_8_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_1_11_10 plane_2_9_9 10829728482 15061646365 14780735019
      (by decide) p (plane_0_4_12_sound p h0) (plane_1_11_10_sound p h1) (plane_2_9_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_10 plane_1_11_19 plane_2_10_10 48321007024 34294140193 46887091617
      (by decide) p (plane_1_11_10_sound p h1) (plane_1_11_19_sound p h1) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_11_10 plane_2_11_11 plane_2_11_13 561792632189 545482288026 187637155215
      (by decide) p (plane_1_11_10_sound p h1) (plane_2_11_11_sound p h2) (plane_2_11_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_11_5 plane_2_12_12 462788033089 68452719217 1212302619693
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_11_5_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_11_5 plane_2_13_13 611127339323 20831107214 1212302619693
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_11_5_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_11_5 plane_2_14_14 597038176555 12377849851 1212302619693
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_11_5_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_11_5 plane_2_15_15 198933311257 4230181198 404100873231
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_11_5_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 4 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_0_4_10 plane_1_0_6 22752306341 282753367353 284726497290
      (by decide) p (plane_0_4_4_sound p h0) (plane_0_4_10_sound p h0) (plane_1_0_6_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_1_1_7 plane_1_1_9 1052207326 8428013 1050521497
      (by decide) p (plane_0_4_4_sound p h0) (plane_1_1_7_sound p h1) (plane_1_1_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_0_4_9 plane_1_2_11 121004392604 273727962933 286122431238
      (by decide) p (plane_0_4_4_sound p h0) (plane_0_4_9_sound p h0) (plane_1_2_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_0_4_10 plane_1_3_11 165657187841 8438500783 189817664860
      (by decide) p (plane_0_4_4_sound p h0) (plane_0_4_10_sound p h0) (plane_1_3_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_4_4 plane_0_4_10 plane_1_4_10 11099928857 94869191801 94908832430
      (by decide) p (plane_0_4_4_sound p h0) (plane_0_4_10_sound p h0) (plane_1_4_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_4_9 plane_1_5_11 plane_1_5_13 112810242211 58574633094 31513008952
      (by decide) p (plane_0_4_9_sound p h0) (plane_1_5_11_sound p h1) (plane_1_5_13_sound p h1))
  · exact complete_4_6 labels p h e0 he
  · exact complete_4_7 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_8_4 plane_1_8_14 1104672086663 80614066653 1131762613157
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_8_4_sound p h1) (plane_1_8_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_0_4_12 plane_1_9_10 281713496990 340592954994 561792632189
      (by decide) p (plane_0_4_10_sound p h0) (plane_0_4_12_sound p h0) (plane_1_9_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_0_4_12 plane_1_10_10 234817143 576561955862 561792632189
      (by decide) p (plane_0_4_10_sound p h0) (plane_0_4_12_sound p h0) (plane_1_10_10_sound p h1))
  · exact complete_4_11 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_4_10 plane_1_12_8 plane_1_12_18 971265191854 152783593819 1059519025874
      (by decide) p (plane_0_4_10_sound p h0) (plane_1_12_8_sound p h1) (plane_1_12_18_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_1_13_13 plane_1_13_19 586247925188 558575523115 8417041069
      (by decide) p (plane_0_4_12_sound p h0) (plane_1_13_13_sound p h1) (plane_1_13_19_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_4_12 plane_1_14_14 plane_1_14_19 286195087637 281223749827 4290134510
      (by decide) p (plane_0_4_12_sound p h0) (plane_1_14_14_sound p h1) (plane_1_14_19_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_4_0 plane_0_4_12 plane_1_15_15 17780407332000000 534921 528190
      (by decide) p (plane_0_4_0_sound p h0) (plane_0_4_12_sound p h0) (plane_1_15_15_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_4
