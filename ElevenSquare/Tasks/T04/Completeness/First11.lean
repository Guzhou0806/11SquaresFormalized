import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 11.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_11_4_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    (e1 : labels 1 = 4)
    (e2 : labels 2 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 4 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 10 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_0_8 4768767144 346360051 9490883243
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_1_9 286092288567 21090479789 569452994580
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_2_10 74160944991 3467060182 142363248645
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_3_3_11 plane_3_3_16 58541425192 123540381302 3025232797
      (by decide) p (plane_0_11_13_sound p h0) (plane_3_3_11_sound p h3) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_0_11_13 plane_3_4_10 1131825858520 3686431551 561792632189
      (by decide) p (plane_0_11_11_sound p h0) (plane_0_11_13_sound p h0) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_5_13 24160503512 2550867439 47454416215
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_6_14 24160503512 2550867439 47454416215
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_7_15 94195258151 1228810517 189817664860
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_2_10_18 plane_3_8_13 274101840469 91202004916 282458329541
      (by decide) p (plane_0_11_11_sound p h0) (plane_2_10_18_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_1_4_13 plane_3_9_17 205334584656 292859327197 280833965361
      (by decide) p (plane_0_11_11_sound p h0) (plane_1_4_13_sound p h1) (plane_3_9_17_sound p h3))
  · refine ⟨(166 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row166]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_4_12 plane_3_11_13 plane_3_11_19 189817664860 94164690509 9788176503
      (by decide) p (plane_1_4_12_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_2_10_18 plane_3_12_14 530596102314 233904112176 282458329541
      (by decide) p (plane_0_11_11_sound p h0) (plane_2_10_18_sound p h2) (plane_3_12_14_sound p h3))
  · refine ⟨(167 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row167]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_10_17 plane_3_14_14 plane_3_14_17 139669658299 41766690707 141095471221
      (by decide) p (plane_2_10_17_sound p h2) (plane_3_14_14_sound p h3) (plane_3_14_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_12 plane_2_10_18 plane_3_15_17 565438832685 18920357693 282557077259
      (by decide) p (plane_1_4_12_sound p h1) (plane_2_10_18_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_11_4_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    (e1 : labels 1 = 4)
    (e2 : labels 2 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 4 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 13 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_13_13 plane_3_0_8 59675557 47687671440 49436485637
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_13_13_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_13_13 plane_3_1_9 520176509 286092288567 296618913822
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_13_13_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_2_13_13 plane_3_2_10 259125349 21187065273 21188841426
      (by decide) p (plane_1_4_4_sound p h1) (plane_2_13_13_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_13 plane_3_3_11 plane_3_3_16 761038527496 805666748654 29600136713
      (by decide) p (plane_2_13_13_sound p h2) (plane_3_3_11_sound p h3) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_2_13_13 plane_3_4_12 8417041069 278839160131 292938243343
      (by decide) p (plane_0_11_11_sound p h0) (plane_2_13_13_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_13_13 plane_3_5_13 2669356303 144963021072 148309456911
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_13_13_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_13_13 plane_3_6_14 2669356303 144963021072 148309456911
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_13_13_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_13 plane_3_7_15 plane_3_7_17 566754254278 578265315311 8417041069
      (by decide) p (plane_2_13_13_sound p h2) (plane_3_7_15_sound p h3) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_3_8_13 plane_3_8_16 246106080017 245232080481 91202004916
      (by decide) p (plane_0_11_11_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_13 plane_2_13_14 plane_3_9_17 144976325411 102667292328 201307041999
      (by decide) p (plane_1_4_13_sound p h1) (plane_2_13_14_sound p h2) (plane_3_9_17_sound p h3))
  · refine ⟨(168 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row168]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_4_12 plane_3_11_13 plane_3_11_19 189817664860 94164690509 9788176503
      (by decide) p (plane_1_4_12_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_2_13_18 plane_3_12_17 49065995824 43574758200 104793484997
      (by decide) p (plane_0_11_11_sound p h0) (plane_2_13_18_sound p h2) (plane_3_12_17_sound p h3))
  · refine ⟨(169 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row169]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(170 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row170]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_4_12 plane_2_13_18 plane_3_15_17 203266315391 18920357693 92227723283
      (by decide) p (plane_1_4_12_sound p h1) (plane_2_13_18_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_11_4_14 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    (e1 : labels 1 = 4)
    (e2 : labels 2 = 14)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 4 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 14 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_0_8 1407478171 95375342880 95374467851
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_1_9 4378363960 286092288567 286123403553
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_2_10 520176509 296643779964 286123403553
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_12 plane_2_14_14 plane_3_3_16 788599788472 821540747462 282557077259
      (by decide) p (plane_1_4_12_sound p h1) (plane_2_14_14_sound p h2) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_2_14_14 plane_3_4_12 4290134510 282494071527 286092288567
      (by decide) p (plane_1_4_4_sound p h1) (plane_2_14_14_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_5_13 9078349777 289926042144 286123403553
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_6_14 9078349777 289926042144 286123403553
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_14_14 plane_3_7_17 plane_3_7_19 1123889340121 67699997 565371132688
      (by decide) p (plane_2_14_14_sound p h2) (plane_3_7_17_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_3_8_13 plane_3_8_16 246106080017 245232080481 91202004916
      (by decide) p (plane_0_11_11_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_9_17 520176509 296643779964 286123403553
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_14_14 plane_2_14_17 plane_3_10_17 41766690707 141095471221 139669658299
      (by decide) p (plane_2_14_14_sound p h2) (plane_2_14_17_sound p h2) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_11_19 1407478171 95375342880 95374467851
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_1 plane_0_11_11 plane_3_12_17 17429903280000000 46388 52819
      (by decide) p (plane_0_11_1_sound p h0) (plane_0_11_11_sound p h0) (plane_3_12_17_sound p h3))
  · refine ⟨(171 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row171]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(172 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row172]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_11_1 plane_1_4_12 plane_3_15_17 75681430772000000 1057261 528190
      (by decide) p (plane_0_11_1_sound p h0) (plane_1_4_12_sound p h1) (plane_3_15_17_sound p h3))

theorem complete_11_8_12 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    (e1 : labels 1 = 8)
    (e2 : labels 2 = 12)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 12 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_0_8 4768767144 346360051 9490883243
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_1_9 286092288567 21090479789 569452994580
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_2_10 74160944991 3467060182 142363248645
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_3_14 155817393453 135112775621 142363248645
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_3_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_8_8 plane_3_4_10 37123299 1430879720 711185161
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_8_8_sound p h1) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_5_13 24160503512 2550867439 47454416215
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_6_14 24160503512 2550867439 47454416215
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_3_7_15 94195258151 1228810517 189817664860
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_3_8_13 plane_3_8_16 246106080017 495236966130 166929547819
      (by decide) p (plane_1_8_4_sound p h1) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_12_17 plane_3_9_15 plane_3_9_17 73763178964 32125196257 7752048309
      (by decide) p (plane_2_12_17_sound p h2) (plane_3_9_15_sound p h3) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_12_17 plane_3_10_18 248405159872 286092288567 40226167464
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_12_17_sound p h2) (plane_3_10_18_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_12_12 plane_3_11_13 plane_3_11_19 189817664860 8438500783 165657187841
      (by decide) p (plane_2_12_12_sound p h2) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_1 plane_1_8_8 plane_3_12_17 12953275728000000 46388 52819
      (by decide) p (plane_0_11_1_sound p h0) (plane_1_8_8_sound p h1) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_12_17 plane_3_13_18 plane_3_13_19 191104724741 70605495944 49065995824
      (by decide) p (plane_2_12_17_sound p h2) (plane_3_13_18_sound p h3) (plane_3_13_19_sound p h3))
  · refine ⟨(173 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row173]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_12_17 plane_3_15_18 39890497256 30493944443 13408722488
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_12_17_sound p h2) (plane_3_15_18_sound p h3))

theorem complete_11_8_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    (e1 : labels 1 = 8)
    (e2 : labels 2 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 13 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_13_13 plane_3_0_8 59675557 47687671440 49436485637
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_13_13_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_13_13 plane_3_1_9 520176509 286092288567 296618913822
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_13_13_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_13_13 plane_3_2_10 3627754886 589557157165 589503107161
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_13_13_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_13 plane_3_3_11 plane_3_3_16 761038527496 805666748654 29600136713
      (by decide) p (plane_2_13_13_sound p h2) (plane_3_3_11_sound p h3) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_13_13 plane_3_4_12 8417041069 561624263596 589503107161
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_13_13_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_13_13 plane_3_5_13 2669356303 144963021072 148309456911
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_13_13_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_13_13 plane_3_6_14 2669356303 144963021072 148309456911
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_13_13_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_13 plane_3_7_15 plane_3_7_17 566754254278 578265315311 8417041069
      (by decide) p (plane_2_13_13_sound p h2) (plane_3_7_15_sound p h3) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_8 plane_3_8_13 plane_3_8_16 246106080017 246453652239 78867780424
      (by decide) p (plane_1_8_8_sound p h1) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_13 plane_3_9_15 plane_3_9_17 590105431712 87603658687 539094743595
      (by decide) p (plane_1_8_13_sound p h1) (plane_3_9_15_sound p h3) (plane_3_9_17_sound p h3))
  · refine ⟨(174 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row174]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_13_13 plane_3_11_14 586422343 180860817 586203387
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_13_13_sound p h2) (plane_3_11_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_8 plane_2_13_18 plane_3_12_17 49065995824 32383189320 92227723283
      (by decide) p (plane_1_8_8_sound p h1) (plane_2_13_18_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_8 plane_3_13_14 plane_3_13_18 279339316598 104793484997 177664844544
      (by decide) p (plane_1_8_8_sound p h1) (plane_3_13_14_sound p h3) (plane_3_13_18_sound p h3))
  · refine ⟨(175 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row175]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(176 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row176]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_11_8_14 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    (e1 : labels 1 = 8)
    (e2 : labels 2 = 14)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 14 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_0_8 1407478171 95375342880 95374467851
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_1_9 4378363960 286092288567 286123403553
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_2_10 520176509 296643779964 286123403553
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_14_14 plane_3_3_11 plane_3_3_16 95129815937 98574973559 3147063011
      (by decide) p (plane_2_14_14_sound p h2) (plane_3_3_11_sound p h3) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_14_14 plane_3_4_12 2145067255 280812131798 284324682913
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_14_14_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_5_13 9078349777 289926042144 286123403553
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_6_14 9078349777 289926042144 286123403553
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_14_14 plane_3_7_17 plane_3_7_19 1123889340121 67699997 565371132688
      (by decide) p (plane_2_14_14_sound p h2) (plane_3_7_17_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_8 plane_3_8_13 plane_3_8_16 246106080017 246453652239 78867780424
      (by decide) p (plane_1_8_8_sound p h1) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_9_17 520176509 296643779964 286123403553
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_8 plane_2_14_17 plane_3_10_18 277812578482 282458329541 92227723283
      (by decide) p (plane_1_8_8_sound p h1) (plane_2_14_17_sound p h2) (plane_3_10_18_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_14 plane_3_11_19 1407478171 95375342880 95374467851
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_1 plane_1_8_8 plane_3_12_17 12953275728000000 46388 52819
      (by decide) p (plane_0_11_1_sound p h0) (plane_1_8_8_sound p h1) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_8 plane_2_14_17 plane_3_13_18 194279197068 104793484997 92227723283
      (by decide) p (plane_1_8_8_sound p h1) (plane_2_14_17_sound p h2) (plane_3_13_18_sound p h3))
  · refine ⟨(177 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row177]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_2_14_17 plane_3_15_18 8987118323 91481833329 97786266987
      (by decide) p (plane_0_11_19_sound p h0) (plane_2_14_17_sound p h2) (plane_3_15_18_sound p h3))

theorem complete_11_9_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    (e1 : labels 1 = 9)
    (e2 : labels 2 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 9 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 10 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_3_0_8 148309456911 10390801530 295155055633
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_3_1_9 296584132177 21090479789 590310111266
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_3_2_10 153758773765 6934120364 295155055633
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_0_11_13 plane_3_3_11 39328026361 245232080481 561792632189
      (by decide) p (plane_0_11_11_sound p h0) (plane_0_11_13_sound p h0) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_0_11_13 plane_3_4_10 1131825858520 3686431551 561792632189
      (by decide) p (plane_0_11_11_sound p h0) (plane_0_11_13_sound p h0) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_3_5_13 150282144431 15305204634 295155055633
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_3_6_14 150282144431 15305204634 295155055633
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_3_7_15 292938243343 3686431551 590310111266
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_2_10_18 plane_3_8_13 274101840469 91202004916 282458329541
      (by decide) p (plane_0_11_11_sound p h0) (plane_2_10_18_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_10 plane_0_11_14 plane_3_9_17 49368533333 100955561673 144193592835
      (by decide) p (plane_0_11_10_sound p h0) (plane_0_11_14_sound p h0) (plane_3_9_17_sound p h3))
  · refine ⟨(178 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row178]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_10_13 plane_3_11_13 plane_3_11_19 142363248645 70440797646 58992250217
      (by decide) p (plane_2_10_13_sound p h2) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_2_10_18 plane_3_12_17 248405159872 43574758200 282458329541
      (by decide) p (plane_0_11_11_sound p h0) (plane_2_10_18_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_10 plane_1_9_8 plane_3_13_14 8154722029 22367449111 21350669565
      (by decide) p (plane_0_11_10_sound p h0) (plane_1_9_8_sound p h1) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_8 plane_2_10_17 plane_3_14_14 282190942442 194257100055 402614083998
      (by decide) p (plane_1_9_8_sound p h1) (plane_2_10_17_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_10_12 plane_2_10_18 plane_3_15_14 14907783697 20962324321 29270657842
      (by decide) p (plane_2_10_12_sound p h2) (plane_2_10_18_sound p h2) (plane_3_15_14_sound p h3))

theorem complete_11_9_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    (e1 : labels 1 = 9)
    (e2 : labels 2 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 9 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 13 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_13_13 plane_3_0_8 59675557 49436485637 51249358108
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_13_13_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_13_13 plane_3_1_9 520176509 296584132177 307496148648
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_13_13_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_2_13_13 plane_3_2_10 3627754886 292859327197 292938243343
      (by decide) p (plane_0_11_11_sound p h0) (plane_2_13_13_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_2_13_13 plane_3_3_11 29600136713 245232080481 292938243343
      (by decide) p (plane_0_11_11_sound p h0) (plane_2_13_13_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_2_13_13 plane_3_4_12 8417041069 278839160131 292938243343
      (by decide) p (plane_0_11_11_sound p h0) (plane_2_13_13_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_13_13 plane_3_5_13 157020959 8840126143 9044004372
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_13_13_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_13_13 plane_3_6_14 157020959 8840126143 9044004372
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_13_13_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_13 plane_3_7_15 plane_3_7_17 566754254278 578265315311 8417041069
      (by decide) p (plane_2_13_13_sound p h2) (plane_3_7_15_sound p h3) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_3_8_13 plane_3_8_16 246106080017 245232080481 91202004916
      (by decide) p (plane_0_11_11_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_14 plane_3_9_14 plane_3_9_17 146115791345 144976325411 37885836517
      (by decide) p (plane_2_13_14_sound p h2) (plane_3_9_14_sound p h3) (plane_3_9_17_sound p h3))
  · refine ⟨(179 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row179]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_13_13 plane_3_11_14 11412680983 3662680931 11826774948
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_13_13_sound p h2) (plane_3_11_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_1_9_4 plane_3_12_17 29353603808 7262459700 47546511199
      (by decide) p (plane_0_11_11_sound p h0) (plane_1_9_4_sound p h1) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_8 plane_2_13_14 plane_3_13_14 20318017992 8154722029 22367449111
      (by decide) p (plane_1_9_8_sound p h1) (plane_2_13_14_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_8 plane_1_9_12 plane_3_14_14 88201229486 194257100055 271974970539
      (by decide) p (plane_1_9_8_sound p h1) (plane_1_9_12_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_12 plane_1_9_17 plane_3_15_14 28769887088 30598113403 40575309727
      (by decide) p (plane_1_9_12_sound p h1) (plane_1_9_17_sound p h1) (plane_3_15_14_sound p h3))

theorem complete_11_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    (e1 : labels 1 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 4 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_0_8 47692487307 2115090599 94908832430
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_1_9 286123403553 12377849851 569452994580
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_2_10 148309456911 10415553607 284726497290
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_3_11 248783313891 68452719217 569452994580
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_4_12 plane_2_4_10 3686431551 1133783611258 562547462351
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_4_12_sound p h1) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_5_13 48337256299 551711303 94908832430
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_6_14 48337256299 551711303 94908832430
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_7_15 94164690509 9788176503 189817664860
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_4_12 plane_2_8_17 201657322281 559925850809 562547462351
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_4_12_sound p h1) (plane_2_8_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_1_4_13 plane_2_9_17 201911123346 292938243343 280833965361
      (by decide) p (plane_0_11_11_sound p h0) (plane_1_4_13_sound p h1) (plane_2_9_17_sound p h2))
  · exact complete_11_4_10 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_2_11_13 plane_2_11_19 189817664860 94164690509 9788176503
      (by decide) p (plane_0_11_11_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_1 plane_1_4_12 plane_2_12_17 17429903280000000 46388 52819
      (by decide) p (plane_0_11_1_sound p h0) (plane_1_4_12_sound p h1) (plane_2_12_17_sound p h2))
  · exact complete_11_4_13 labels p h e0 e1 he
  · exact complete_11_4_14 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_11_1 plane_0_11_11 plane_2_15_17 75681430772000000 1057261 528190
      (by decide) p (plane_0_11_1_sound p h0) (plane_0_11_11_sound p h0) (plane_2_15_17_sound p h2))

theorem complete_11_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    (e1 : labels 1 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_0_8 47692487307 2115090599 94908832430
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_1_9 286123403553 12377849851 569452994580
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_2_10 148309456911 10415553607 284726497290
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_3_11 248783313891 68452719217 569452994580
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_4_12 94164690509 9788176503 189817664860
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_4_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_5_13 48337256299 551711303 94908832430
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_6_14 48337256299 551711303 94908832430
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_2_7_15 94164690509 9788176503 189817664860
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_14 plane_0_11_19 plane_2_8_17 9931292687 9858040810 13624877678
      (by decide) p (plane_0_11_14_sound p h0) (plane_0_11_19_sound p h0) (plane_2_8_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_1_8_13 plane_2_9_17 90948203851 296618913822 274086016275
      (by decide) p (plane_0_11_19_sound p h0) (plane_1_8_13_sound p h1) (plane_2_9_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_8_8 plane_1_8_13 plane_2_10_17 70761576674 63443117992 90658323513
      (by decide) p (plane_1_8_8_sound p h1) (plane_1_8_13_sound p h1) (plane_2_10_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_8_8 plane_2_11_13 plane_2_11_19 189817664860 94195258151 1228810517
      (by decide) p (plane_1_8_8_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact complete_11_8_12 labels p h e0 e1 he
  · exact complete_11_8_13 labels p h e0 e1 he
  · exact complete_11_8_14 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_8_8 plane_2_15_15 plane_2_15_17 565595488056 6587121193 282585774453
      (by decide) p (plane_1_8_8_sound p h1) (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2))

theorem complete_11_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    (e1 : labels 1 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 9 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_2_0_8 148321889982 6345271797 295155055633
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_2_1_9 296610908583 12377849851 590310111266
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_2_2_10 153748074324 10415553607 295155055633
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_2_3_11 257938437109 68452719217 590310111266
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_2_4_12 292859327197 29364529509 590310111266
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_2_4_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_2_5_13 150324095006 1655133909 295155055633
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_2_6_14 150324095006 1655133909 295155055633
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_9_17 plane_2_7_15 292859327197 29364529509 590310111266
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_9_17_sound p h1) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_14 plane_1_9_17 plane_2_8_17 216547944797 207018857010 296729705558
      (by decide) p (plane_0_11_14_sound p h0) (plane_1_9_17_sound p h1) (plane_2_8_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_14 plane_2_9_14 plane_2_9_17 146115791345 47614852103 123563208361
      (by decide) p (plane_0_11_14_sound p h0) (plane_2_9_14_sound p h2) (plane_2_9_17_sound p h2))
  · exact complete_11_9_10 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_2_11_13 plane_2_11_19 189817664860 94164690509 9788176503
      (by decide) p (plane_0_11_11_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_9_12 plane_1_9_17 plane_2_12_17 41390492312 225578898288 284027168089
      (by decide) p (plane_1_9_12_sound p h1) (plane_1_9_17_sound p h1) (plane_2_12_17_sound p h2))
  · exact complete_11_9_13 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_9_8 plane_2_14_14 plane_2_14_17 279339316598 204073209213 198540874785
      (by decide) p (plane_1_9_8_sound p h1) (plane_2_14_14_sound p h2) (plane_2_14_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_1_9_4 plane_2_15_17 538719090894 18920357693 285279067194
      (by decide) p (plane_0_11_11_sound p h0) (plane_1_9_4_sound p h1) (plane_2_15_17_sound p h2))

theorem complete_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 11 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_11_1 plane_0_11_11 plane_1_0_8 17780407332000000 534921 528190
      (by decide) p (plane_0_11_1_sound p h0) (plane_0_11_11_sound p h0) (plane_1_0_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_1_1_4 plane_1_1_9 286195087637 4290134510 281223749827
      (by decide) p (plane_0_11_11_sound p h0) (plane_1_1_4_sound p h1) (plane_1_1_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_1_2_4 plane_1_2_10 586247925188 8417041069 558575523115
      (by decide) p (plane_0_11_11_sound p h0) (plane_1_2_4_sound p h1) (plane_1_2_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_0_11_13 plane_1_3_10 652326497738 235732358179 561792632189
      (by decide) p (plane_0_11_11_sound p h0) (plane_0_11_13_sound p h0) (plane_1_3_10_sound p h1))
  · exact complete_11_4 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_11_11 plane_0_11_13 plane_1_5_13 576561955862 234817143 561792632189
      (by decide) p (plane_0_11_11_sound p h0) (plane_0_11_13_sound p h0) (plane_1_5_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_6_9 plane_1_6_14 144488640871 288280977931 117984500434
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_6_9_sound p h1) (plane_1_6_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_1_7_9 plane_1_7_19 1104672086663 1131762613157 80614066653
      (by decide) p (plane_0_11_13_sound p h0) (plane_1_7_9_sound p h1) (plane_1_7_19_sound p h1))
  · exact complete_11_8 labels p h e0 he
  · exact complete_11_9 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_1_10_13 70440797646 58992250217 142363248645
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_1_10_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_1_11_13 94869191801 11099928857 94908832430
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_1_11_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_1_12_12 8438500783 165657187841 189817664860
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_1_12_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_11_14 plane_0_11_19 plane_1_13_12 273727962933 121004392604 286122431238
      (by decide) p (plane_0_11_14_sound p h0) (plane_0_11_19_sound p h0) (plane_1_13_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_11_19 plane_1_14_14 plane_1_14_16 1052207326 1050521497 8428013
      (by decide) p (plane_0_11_19_sound p h0) (plane_1_14_14_sound p h1) (plane_1_14_16_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_11_13 plane_0_11_19 plane_1_15_17 282753367353 22752306341 284726497290
      (by decide) p (plane_0_11_13_sound p h0) (plane_0_11_19_sound p h0) (plane_1_15_17_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_11
