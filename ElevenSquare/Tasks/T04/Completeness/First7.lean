import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 7.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_7_0_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    (e1 : labels 1 = 0)
    (e2 : labels 2 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 0 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 10 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_7_7 plane_1_0_6 plane_3_0_8 2226553614 249168225957 492686929159
      (by decide) p (plane_0_7_7_sound p h0) (plane_1_0_6_sound p h1) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_3_1_8 plane_3_1_9 286038658844 1917121227 562870354603
      (by decide) p (plane_1_0_6_sound p h1) (plane_3_1_8_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_3_2_4 plane_3_2_10 293123962594 4966236753 558968563873
      (by decide) p (plane_1_0_6_sound p h1) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_3_3_16 142571987185 254571102501 94265914676
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_7 plane_1_0_6 plane_3_4_12 18920357693 245232080481 492686929159
      (by decide) p (plane_0_7_7_sound p h0) (plane_1_0_6_sound p h1) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_3_5_13 145011768897 3615241625 282797744028
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_10_18 plane_3_6_8 569141090689 12690543594 286092288567
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_10_18_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_3_7_17 188807480585 365596738813 188531829352
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_3_7_17_sound p h3))
  · refine ⟨(93 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row93]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_7_7 plane_1_0_9 plane_3_9_17 201389209616 257938437109 265998687433
      (by decide) p (plane_0_7_7_sound p h0) (plane_1_0_9_sound p h1) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_3_10_17 94168568283 275461549151 282797744028
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_3_11_13 plane_3_11_19 94908832430 47692487307 2115090599
      (by decide) p (plane_1_0_8_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · refine ⟨(94 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row94]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(95 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row95]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_10_18 plane_3_14_16 526217738354 57560099523 286092288567
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_10_18_sound p h2) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_10_18 plane_3_15_17 3695678645 14552638 1869884239
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_10_18_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_7_0_14 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    (e1 : labels 1 = 0)
    (e2 : labels 2 = 14)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 0 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 14 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_14_14 plane_3_0_8 1407478171 95384974614 95364096189
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_14_14_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_14_14 plane_3_1_9 4378363960 286123403553 286092288567
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_14_14_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_14_14 plane_3_2_10 520176509 296618913822 286092288567
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_14_14_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_14_14 plane_3_3_16 788599788472 855431923110 286092288567
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_14_14_sound p h2) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_7 plane_2_14_14 plane_3_4_12 4290134510 245232080481 248740136971
      (by decide) p (plane_0_7_7_sound p h0) (plane_2_14_14_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_14_14 plane_3_5_13 9078349777 290023537794 286092288567
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_14_14_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_14_14 plane_3_6_14 9078349777 290023537794 286092288567
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_14_14_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_14_14 plane_3_7_17 565371132688 566422441755 286092288567
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_14_14_sound p h2) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_7 plane_2_14_14 plane_3_8_16 25176504088 214074416447 248740136971
      (by decide) p (plane_0_7_7_sound p h0) (plane_2_14_14_sound p h2) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_14_14 plane_3_9_17 520176509 296618913822 286092288567
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_14_14_sound p h2) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_14_14 plane_3_10_17 282190942442 188337136566 286092288567
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_14_14_sound p h2) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_3_11_13 plane_3_11_19 94908832430 47692487307 2115090599
      (by decide) p (plane_1_0_8_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · refine ⟨(96 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row96]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(97 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row97]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_7_1 plane_1_0_8 plane_3_14_16 230240398092000000 984719 534921
      (by decide) p (plane_0_7_1_sound p h0) (plane_1_0_8_sound p h1) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_1 plane_1_0_8 plane_3_15_17 8906214456000000 1057261 534921
      (by decide) p (plane_0_7_1_sound p h0) (plane_1_0_8_sound p h1) (plane_3_15_17_sound p h3))

theorem complete_7_0_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    (e1 : labels 1 = 0)
    (e2 : labels 2 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 0 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 15 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_0_8 225914969 15897495769 15895890480
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_1_9 1407478171 95374467851 95375342880
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_2_10 59675557 49436485637 47687671440
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_3_16 26274168685 28514397437 9537534288
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_7 plane_2_15_15 plane_3_4_12 1481700611 81744026827 82927771297
      (by decide) p (plane_0_7_7_sound p h0) (plane_2_15_15_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_5_13 1486807019 48337256299 47687671440
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_6_14 1486807019 48337256299 47687671440
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_7_17 37675206821 37761496117 19075068576
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(98 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row98]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_9_17 59675557 49436485637 47687671440
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_10_17 47020207321 31389522761 47687671440
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_3_11_13 plane_3_11_19 94908832430 47692487307 2115090599
      (by decide) p (plane_1_0_8_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · refine ⟨(99 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row99]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(100 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row100]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_7_1 plane_1_0_8 plane_3_14_16 230240398092000000 984719 534921
      (by decide) p (plane_0_7_1_sound p h0) (plane_1_0_8_sound p h1) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_1 plane_1_0_8 plane_3_15_17 8906214456000000 1057261 534921
      (by decide) p (plane_0_7_1_sound p h0) (plane_1_0_8_sound p h1) (plane_3_15_17_sound p h3))

theorem complete_7_4_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    (e1 : labels 1 = 4)
    (e2 : labels 2 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 4 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 10 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_1_4_10 plane_3_0_8 2115090599 47692487307 94908832430
      (by decide) p (plane_1_4_4_sound p h1) (plane_1_4_10_sound p h1) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_1_4_10 plane_3_1_9 12377849851 286123403553 569452994580
      (by decide) p (plane_1_4_4_sound p h1) (plane_1_4_10_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_1_4_10 plane_3_2_10 10415553607 148309456911 284726497290
      (by decide) p (plane_1_4_4_sound p h1) (plane_1_4_10_sound p h1) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_10 plane_3_3_11 plane_3_3_16 761038527496 1506608386910 68452719217
      (by decide) p (plane_1_4_10_sound p h1) (plane_3_3_11_sound p h3) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_1_4_10 plane_3_4_12 9788176503 94164690509 189817664860
      (by decide) p (plane_1_4_4_sound p h1) (plane_1_4_10_sound p h1) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_1_4_10 plane_3_5_13 551711303 48337256299 94908832430
      (by decide) p (plane_1_4_4_sound p h1) (plane_1_4_10_sound p h1) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_10 plane_3_6_8 plane_3_6_14 288682233706 1655133909 566891805629
      (by decide) p (plane_1_4_10_sound p h1) (plane_3_6_8_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_1_4_10 plane_3_7_17 1083587974535 568012055777 562547462351
      (by decide) p (plane_0_7_15_sound p h0) (plane_1_4_10_sound p h1) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_9 plane_3_8_13 plane_3_8_16 35158011431 7750937394 43178365888
      (by decide) p (plane_1_4_9_sound p h1) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_10 plane_1_4_9 plane_3_9_17 95229704206 90948203851 175725312954
      (by decide) p (plane_0_7_10_sound p h0) (plane_1_4_9_sound p h1) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_10 plane_0_7_15 plane_3_10_17 63443117992 70761576674 90658323513
      (by decide) p (plane_0_7_10_sound p h0) (plane_0_7_15_sound p h0) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_3_11_13 plane_3_11_19 189817664860 94195258151 1228810517
      (by decide) p (plane_0_7_15_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_2_10_18 plane_3_12_17 248405159872 40226167464 286092288567
      (by decide) p (plane_1_4_4_sound p h1) (plane_2_10_18_sound p h2) (plane_3_12_17_sound p h3))
  · refine ⟨(101 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row101]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_2_10_18 plane_3_14_17 277812578482 92227723283 282458329541
      (by decide) p (plane_0_7_15_sound p h0) (plane_2_10_18_sound p h2) (plane_3_14_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_3_15_15 plane_3_15_17 565595488056 6587121193 282585774453
      (by decide) p (plane_0_7_15_sound p h0) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_7_4_14 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    (e1 : labels 1 = 4)
    (e2 : labels 2 = 14)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 4 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 14 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_14_14 plane_3_0_8 4222434513 568711803093 568581733094
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_14_14 plane_3_1_9 2189181980 284324682913 284290866547
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_14_14 plane_3_2_10 520176509 589503107161 568581733094
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_14_14 plane_3_3_16 394299894236 850567411738 284290866547
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_2_14_14 plane_3_4_12 4290134510 282494071527 286092288567
      (by decide) p (plane_1_4_4_sound p h1) (plane_2_14_14_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_14_14 plane_3_5_13 9078349777 576406739029 568581733094
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_14_14 plane_3_6_14 9078349777 576406739029 568581733094
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_14_14 plane_3_7_17 282685566344 563230003567 284290866547
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_2_14_14 plane_3_8_16 25176504088 248783313891 286092288567
      (by decide) p (plane_1_4_4_sound p h1) (plane_2_14_14_sound p h2) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_14_14 plane_3_9_17 520176509 589503107161 568581733094
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_2_14_14 plane_3_10_17 282190942442 190329353976 282458329541
      (by decide) p (plane_0_7_15_sound p h0) (plane_2_14_14_sound p h2) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_14_14 plane_3_11_19 4222434513 568711803093 568581733094
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_14_14_sound p h2) (plane_3_11_19_sound p h3))
  · refine ⟨(102 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row102]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(103 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row103]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(104 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row104]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_2_14_14 plane_3_15_17 565438832685 6587121193 282458329541
      (by decide) p (plane_0_7_15_sound p h0) (plane_2_14_14_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_7_4_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    (e1 : labels 1 = 4)
    (e2 : labels 2 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 4 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 15 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_0_8 193641402 27081514433 27078523589
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_1_9 4222434513 568649365826 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_2_10 358053342 589503107161 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_3_14 257691356040 1246184356094 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_3_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_2_15_15 plane_3_4_12 1481700611 94164690509 95375342880
      (by decide) p (plane_1_4_4_sound p h1) (plane_2_15_15_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_5_13 8920842114 576406739029 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_6_14 8920842114 576406739029 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_15 plane_2_15_17 plane_3_7_17 366465071157 188376034105 188531829352
      (by decide) p (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_2_15_14 plane_3_8_16 265998687433 248783313891 194610455238
      (by decide) p (plane_1_4_4_sound p h1) (plane_2_15_14_sound p h2) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_9_17 358053342 589503107161 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_15 plane_2_15_17 plane_3_10_17 181086258647 141060621963 282797744028
      (by decide) p (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_17 plane_3_11_13 plane_3_11_19 284726497290 282753367353 22752306341
      (by decide) p (plane_2_15_17_sound p h2) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_2_15_18 plane_3_12_17 39890497256 13408722488 30493944443
      (by decide) p (plane_1_4_4_sound p h1) (plane_2_15_18_sound p h2) (plane_3_12_17_sound p h3))
  · refine ⟨(105 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row105]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_2_15_18 plane_3_14_17 8987118323 97786266987 91481833329
      (by decide) p (plane_1_4_4_sound p h1) (plane_2_15_18_sound p h2) (plane_3_14_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_1 plane_2_15_17 plane_3_15_17 93400000000 1 1
      (by decide) p (plane_0_7_1_sound p h0) (plane_2_15_17_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_7_5_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 10 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_10_10 plane_3_0_8 8920842114 568711803093 576194818729
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_10_10_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_10_10 plane_3_1_9 9078349777 568649365826 576194818729
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_10_10_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_10_10 plane_3_2_10 5338712606 589503107161 576194818729
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_10_10_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_10_10 plane_3_3_11 plane_3_3_16 58541425192 62541817438 1652174849
      (by decide) p (plane_2_10_10_sound p h2) (plane_3_3_11_sound p h3) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_9 plane_0_7_19 plane_3_4_12 561424934584 11327968305 1104672086663
      (by decide) p (plane_0_7_9_sound p h0) (plane_0_7_19_sound p h0) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_10_10 plane_3_5_13 731820150 30337196791 30326043091
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_10_10_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_10 plane_3_6_8 plane_3_6_14 577364467412 80715855727 549168719577
      (by decide) p (plane_0_7_10_sound p h0) (plane_3_6_8_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_10_10 plane_3_7_17 30638709769 30706594841 15457684384
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_10_10_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(106 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row106]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_7_10 plane_3_9_12 plane_3_9_17 284027168089 90948203851 235449636515
      (by decide) p (plane_0_7_10_sound p h0) (plane_3_9_12_sound p h3) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_10 plane_1_5_13 plane_3_10_17 65190374802 70761576674 93067799921
      (by decide) p (plane_0_7_10_sound p h0) (plane_1_5_13_sound p h1) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_3_11_13 plane_3_11_19 94908832430 48337256299 551711303
      (by decide) p (plane_1_5_13_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · refine ⟨(107 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row107]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(108 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row108]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_10_18 plane_3_14_17 277812578482 94423090859 289889229815
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_10_18_sound p h2) (plane_3_14_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_3_15_15 plane_3_15_17 282797744028 3615241625 145011768897
      (by decide) p (plane_1_5_13_sound p h1) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_7_5_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 15 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_0_8 193641402 27081514433 27078523589
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_1_9 4222434513 568649365826 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_2_10 358053342 589503107161 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_3_14 257691356040 1246184356094 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_3_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_5 plane_2_15_15 plane_3_4_12 4445101833 282458329541 286092288567
      (by decide) p (plane_1_5_5_sound p h1) (plane_2_15_15_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_5_13 8920842114 576406739029 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_6_14 8920842114 576406739029 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_15 plane_2_15_17 plane_3_7_17 366465071157 188376034105 188531829352
      (by decide) p (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(109 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row109]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_2_15_15 plane_3_9_17 358053342 589503107161 568648995369
      (by decide) p (plane_0_7_19_sound p h0) (plane_2_15_15_sound p h2) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_15 plane_2_15_17 plane_3_10_17 181086258647 141060621963 282797744028
      (by decide) p (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_17 plane_3_11_13 plane_3_11_19 284726497290 282753367353 22752306341
      (by decide) p (plane_2_15_17_sound p h2) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_4 plane_2_15_14 plane_3_12_12 265998687433 194526752133 153753283400
      (by decide) p (plane_1_5_4_sound p h1) (plane_2_15_14_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_4 plane_2_15_14 plane_3_13_16 16091708513 27631156413 19219160425
      (by decide) p (plane_1_5_4_sound p h1) (plane_2_15_14_sound p h2) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_8 plane_2_15_17 plane_3_14_17 203266315391 246619005718 568871204030
      (by decide) p (plane_1_5_8_sound p h1) (plane_2_15_17_sound p h2) (plane_3_14_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_8 plane_2_15_17 plane_3_15_17 2468704435 56478747583 56887120403
      (by decide) p (plane_1_5_8_sound p h1) (plane_2_15_17_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_7_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    (e1 : labels 1 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 0 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_2_0_6 427660489 46569354854 23566478669
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_2_1_9 plane_2_1_15 564756396848 1094452375015 10571859773
      (by decide) p (plane_1_0_6_sound p h1) (plane_2_1_9_sound p h2) (plane_2_1_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_7 plane_1_0_6 plane_2_2_10 3015872044 258269678195 492686929159
      (by decide) p (plane_0_7_7_sound p h0) (plane_1_0_6_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_2_3_11 249168225957 48098237513 565595488056
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_2_4_10 5195400765 281228124047 141398872014
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_2_5_15 25892303767 92085352899 47132957338
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_2_5_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_2_6_15 33068411457 91497157105 94265914676
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_2_6_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_2_7_15 282585774453 6587121193 565595488056
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_8_4 plane_2_8_14 1104672086663 28121870751 568711803093
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_2_9_15 5195400765 281228124047 141398872014
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_2_9_15_sound p h2))
  · exact complete_7_0_10 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_7_7 plane_1_0_9 plane_2_11_19 194610455238 248783313891 265998687433
      (by decide) p (plane_0_7_7_sound p h0) (plane_1_0_9_sound p h1) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_2_12_18 65045933361 1039767016309 565595488056
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_13_13 plane_2_13_19 146561981297 2565962934 74160944991
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact complete_7_0_14 labels p h e0 e1 he
  · exact complete_7_0_15 labels p h e0 e1 he

theorem complete_7_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    (e1 : labels 1 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 4 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_7_17 plane_2_0_6 plane_2_0_8 188531829352 188807480585 365596738813
      (by decide) p (plane_0_7_17_sound p h0) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_1_4_10 plane_2_1_9 21090479789 286092288567 569452994580
      (by decide) p (plane_1_4_4_sound p h1) (plane_1_4_10_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_1_4_10 plane_2_2_10 3467060182 74160944991 142363248645
      (by decide) p (plane_1_4_4_sound p h1) (plane_1_4_10_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_19 plane_1_4_10 plane_2_3_11 39328026361 495236966130 1131762613157
      (by decide) p (plane_0_7_19_sound p h0) (plane_1_4_10_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_0_7_17 plane_2_4_10 1083587974535 29364529509 566754254278
      (by decide) p (plane_0_7_15_sound p h0) (plane_0_7_17_sound p h0) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_1_4_10 plane_2_5_13 2550867439 24160503512 47454416215
      (by decide) p (plane_1_4_4_sound p h1) (plane_1_4_10_sound p h1) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_1_4_10 plane_2_6_14 2550867439 24160503512 47454416215
      (by decide) p (plane_1_4_4_sound p h1) (plane_1_4_10_sound p h1) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_4_4 plane_1_4_10 plane_2_7_15 1228810517 94195258151 189817664860
      (by decide) p (plane_1_4_4_sound p h1) (plane_1_4_10_sound p h1) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_1_4_10 plane_2_8_14 157843125829 5200802625 80363923193
      (by decide) p (plane_0_7_15_sound p h0) (plane_1_4_10_sound p h1) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_10 plane_2_9_15 plane_2_9_17 590105431712 87603658687 539094743595
      (by decide) p (plane_0_7_10_sound p h0) (plane_2_9_15_sound p h2) (plane_2_9_17_sound p h2))
  · exact complete_7_4_10 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_4_9 plane_2_11_13 plane_2_11_19 94908832430 15252595567 96015449549
      (by decide) p (plane_1_4_9_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_1_4_10 plane_2_12_18 1044483374653 72410295677 562547462351
      (by decide) p (plane_0_7_15_sound p h0) (plane_1_4_10_sound p h1) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_2_13_14 plane_2_13_18 279339316598 104793484997 177664844544
      (by decide) p (plane_0_7_15_sound p h0) (plane_2_13_14_sound p h2) (plane_2_13_18_sound p h2))
  · exact complete_7_4_14 labels p h e0 e1 he
  · exact complete_7_4_15 labels p h e0 e1 he

theorem complete_7_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    (e1 : labels 1 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_7_17 plane_2_0_6 plane_2_0_8 188531829352 188807480585 365596738813
      (by decide) p (plane_0_7_17_sound p h0) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_9 plane_0_7_19 plane_2_1_9 568581733094 19913735575 1104672086663
      (by decide) p (plane_0_7_9_sound p h0) (plane_0_7_19_sound p h0) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_9 plane_0_7_19 plane_2_2_10 589557157165 28457152733 1104672086663
      (by decide) p (plane_0_7_9_sound p h0) (plane_0_7_19_sound p h0) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_9 plane_0_7_19 plane_2_3_11 495236966130 73661771269 1104672086663
      (by decide) p (plane_0_7_9_sound p h0) (plane_0_7_19_sound p h0) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_17 plane_1_5_13 plane_2_4_10 30610409268 1083587974535 582135485611
      (by decide) p (plane_0_7_17_sound p h0) (plane_1_5_13_sound p h1) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_9 plane_0_7_19 plane_2_5_13 576194818729 11163951429 1104672086663
      (by decide) p (plane_0_7_9_sound p h0) (plane_0_7_19_sound p h0) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_9 plane_0_7_19 plane_2_6_14 576194818729 11163951429 1104672086663
      (by decide) p (plane_0_7_9_sound p h0) (plane_0_7_19_sound p h0) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_9 plane_0_7_19 plane_2_7_15 561624263596 36405618375 1104672086663
      (by decide) p (plane_0_7_9_sound p h0) (plane_0_7_19_sound p h0) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_17 plane_1_5_13 plane_2_8_14 37825715679 1042866578459 582135485611
      (by decide) p (plane_0_7_17_sound p h0) (plane_1_5_13_sound p h1) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_7_10 plane_2_9_15 plane_2_9_17 590105431712 87603658687 539094743595
      (by decide) p (plane_0_7_10_sound p h0) (plane_2_9_15_sound p h2) (plane_2_9_17_sound p h2))
  · exact complete_7_5_10 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_7_7 plane_0_7_10 plane_2_11_14 43178365888 7750937394 35158011431
      (by decide) p (plane_0_7_7_sound p h0) (plane_0_7_10_sound p h0) (plane_2_11_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_12_12 plane_2_12_18 452528907170 74753504753 252961440741
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_5_8 plane_1_5_13 plane_2_13_14 10117034367 12250414744 16021510315
      (by decide) p (plane_1_5_8_sound p h1) (plane_1_5_13_sound p h1) (plane_2_13_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_5_4 plane_1_5_8 plane_2_14_14 91348355030 194743933537 286122431238
      (by decide) p (plane_1_5_4_sound p h1) (plane_1_5_8_sound p h1) (plane_2_14_14_sound p h2))
  · exact complete_7_5_15 labels p h e0 e1 he

theorem complete_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 7 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact complete_7_0 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_7_7 plane_1_1_4 plane_1_1_9 286195087637 25176504088 240822183345
      (by decide) p (plane_0_7_7_sound p h0) (plane_1_1_4_sound p h1) (plane_1_1_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_7_7 plane_0_7_10 plane_1_2_4 164242869823 492686929159 246106080017
      (by decide) p (plane_0_7_7_sound p h0) (plane_0_7_10_sound p h0) (plane_1_2_4_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_7_9 plane_0_7_19 plane_1_3_5 1047812442533 163617988624 1104672086663
      (by decide) p (plane_0_7_9_sound p h0) (plane_0_7_19_sound p h0) (plane_1_3_5_sound p h1))
  · exact complete_7_4 labels p h e0 he
  · exact complete_7_5 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_7_9 plane_0_7_15 plane_1_6_9 281478679847 238179111413 548479375832
      (by decide) p (plane_0_7_9_sound p h0) (plane_0_7_15_sound p h0) (plane_1_6_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_7_9 plane_0_7_15 plane_1_7_6 138253947245 216155984859 274239687916
      (by decide) p (plane_0_7_9_sound p h0) (plane_0_7_15_sound p h0) (plane_1_7_6_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_7_14 plane_0_7_15 plane_1_8_8 1061925995 22360472547 23774018908
      (by decide) p (plane_0_7_14_sound p h0) (plane_0_7_15_sound p h0) (plane_1_8_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_7_10 plane_0_7_15 plane_1_9_8 31203773929 11497565201 30219441171
      (by decide) p (plane_0_7_10_sound p h0) (plane_0_7_15_sound p h0) (plane_1_9_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_1_10_10 plane_1_10_12 564051211055 549569533268 234817143
      (by decide) p (plane_0_7_15_sound p h0) (plane_1_10_10_sound p h1) (plane_1_10_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_7_9 plane_0_7_19 plane_1_11_13 1131762613157 80614066653 1104672086663
      (by decide) p (plane_0_7_9_sound p h0) (plane_0_7_19_sound p h0) (plane_1_11_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_7_14 plane_0_7_19 plane_1_12_12 57673997591 208324689842 562950255921
      (by decide) p (plane_0_7_14_sound p h0) (plane_0_7_19_sound p h0) (plane_1_12_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_7_15 plane_0_7_17 plane_1_13_13 578265315311 8417041069 566754254278
      (by decide) p (plane_0_7_15_sound p h0) (plane_0_7_17_sound p h0) (plane_1_13_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_7_14 plane_0_7_19 plane_1_14_14 67699997 283180190246 562950255921
      (by decide) p (plane_0_7_14_sound p h0) (plane_0_7_19_sound p h0) (plane_1_14_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_7_17 plane_1_15_15 plane_1_15_17 188531829352 366465071157 188376034105
      (by decide) p (plane_0_7_17_sound p h0) (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_7
