import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 3.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_3_0_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 3)
    (e1 : labels 1 = 0)
    (e2 : labels 2 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 3 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_3_2 plane_2_15_15 plane_3_4_12 17780407332000000 528190 534921
      (by decide) p (plane_0_3_2_sound p h0) (plane_2_15_15_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_5_13 1486807019 48337256299 47687671440
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_6_14 1486807019 48337256299 47687671440
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_7_17 37675206821 37761496117 19075068576
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(34 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row34]
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
  · refine ⟨(35 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row35]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_0_3_11 plane_3_13_16 7119365177 26251808648 27443859744
      (by decide) p (plane_0_3_6_sound p h0) (plane_0_3_11_sound p h0) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_1 plane_1_0_8 plane_3_14_16 230240398092000000 984719 534921
      (by decide) p (plane_0_3_1_sound p h0) (plane_1_0_8_sound p h1) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_1 plane_1_0_8 plane_3_15_17 8906214456000000 1057261 534921
      (by decide) p (plane_0_3_1_sound p h0) (plane_1_0_8_sound p h1) (plane_3_15_17_sound p h3))

theorem complete_3_1_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 3)
    (e1 : labels 1 = 1)
    (e2 : labels 2 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 3 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 1 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 11 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_3_2 plane_2_11_11 plane_3_0_8 17780407332000000 534921 528190
      (by decide) p (plane_0_3_2_sound p h0) (plane_2_11_11_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_11 plane_3_1_8 plane_3_1_9 143019329422 2145067255 138389323997
      (by decide) p (plane_2_11_11_sound p h2) (plane_3_1_8_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_11 plane_3_2_12 541387309342 566664611867 282557077259
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_11_sound p h2) (plane_3_2_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_19 plane_3_3_5 526311269997 57265570853 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_19_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_1_9 plane_3_4_12 282458329541 48652965083 526217738354
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_1_9_sound p h1) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_11 plane_3_5_8 281068782504 95737115210 282557077259
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_11_sound p h2) (plane_3_5_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_19 plane_3_6_8 569215150806 12377849851 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_11 plane_3_7_17 541387309342 566664611867 282557077259
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_11_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(36 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row36]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_1_1_9 plane_3_9_12 44100614743 112789449144 124202579936
      (by decide) p (plane_0_3_6_sound p h0) (plane_1_1_9_sound p h1) (plane_3_9_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_3_10_10 plane_3_10_17 280092222898 188469167116 289994215265
      (by decide) p (plane_1_1_9_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_3_11_13 plane_3_11_19 569452994580 286123403553 12377849851
      (by decide) p (plane_1_1_9_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_19 plane_3_12_12 1489147197 14631772763 16828958151
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_3_13_13 plane_3_13_16 257471966024 40357234280 296584132177
      (by decide) p (plane_1_1_9_sound p h1) (plane_3_13_13_sound p h3) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_19 plane_3_14_16 526311269997 57265570853 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_19_sound p h2) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_19 plane_3_15_17 188502244902 639040409 95364096189
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_3_1_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 3)
    (e1 : labels 1 = 1)
    (e2 : labels 2 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 3 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 1 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 15 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_0_8 1355489814 95374467851 95364096189
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_1_9 4222434513 286091972249 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_2_10 358053342 296584132177 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_3_16 788225060550 855761983118 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_2 plane_2_15_15 plane_3_4_12 17780407332000000 528190 534921
      (by decide) p (plane_0_3_2_sound p h0) (plane_2_15_15_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_5_13 8920842114 289994215265 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_3_6_8 plane_3_6_14 577364467412 289994215265 12377849851
      (by decide) p (plane_1_1_9_sound p h1) (plane_3_6_8_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_7_17 565128102315 566664611867 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(37 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row37]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_9_12 274086016275 88201229486 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_9_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_10_17 282121243926 188469167116 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_3_11_13 plane_3_11_19 569452994580 286123403553 12377849851
      (by decide) p (plane_1_1_9_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_2 plane_1_1_4 plane_3_12_12 108426769676000000 232722 268211
      (by decide) p (plane_0_3_2_sound p h0) (plane_1_1_4_sound p h1) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_13_16 248412460584 40357234280 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_4 plane_1_1_9 plane_3_14_16 57265570853 508188953156 286195087637
      (by decide) p (plane_1_1_4_sound p h1) (plane_1_1_9_sound p h1) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_4 plane_1_1_9 plane_3_15_17 1917121227 565096908217 286195087637
      (by decide) p (plane_1_1_4_sound p h1) (plane_1_1_9_sound p h1) (plane_3_15_17_sound p h3))

theorem complete_3_5_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 3)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 3 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 10 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_3_16 plane_2_10_10 plane_3_0_8 4460421057 422157964509 440007817363
      (by decide) p (plane_0_3_16_sound p h0) (plane_2_10_10_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_16 plane_2_10_10 plane_3_1_9 9078349777 843792037362 880015634726
      (by decide) p (plane_0_3_16_sound p h0) (plane_2_10_10_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_16 plane_2_10_10 plane_3_2_10 2669356303 442908082269 440007817363
      (by decide) p (plane_0_3_16_sound p h0) (plane_2_10_10_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_2_10_10 plane_3_3_16 813043626694 813527881814 251662704291
      (by decide) p (plane_0_3_11_sound p h0) (plane_2_10_10_sound p h2) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_1_5_5 plane_3_4_12 282458329541 43574758200 248405159872
      (by decide) p (plane_0_3_6_sound p h0) (plane_1_5_5_sound p h1) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_10_10 plane_3_5_13 19258425 407236793 406781168
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_10_10_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_10 plane_3_6_8 plane_3_6_14 144341116853 83419324117 127460173304
      (by decide) p (plane_0_3_10_sound p h0) (plane_3_6_8_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_2_10_10 plane_3_7_17 582135485611 542498543951 251662704291
      (by decide) p (plane_0_3_11_sound p h0) (plane_2_10_10_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(38 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row38]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_3_9_12 plane_3_9_17 284027168089 41390492312 225578898288
      (by decide) p (plane_0_3_6_sound p h0) (plane_3_9_12_sound p h3) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_10 plane_2_10_18 plane_3_10_17 282190942442 23566568890 336941366457
      (by decide) p (plane_0_3_10_sound p h0) (plane_2_10_18_sound p h2) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_0_3_16 plane_3_11_13 123540381302 3025232797 58541425192
      (by decide) p (plane_0_3_11_sound p h0) (plane_0_3_16_sound p h0) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_2_10_19 plane_3_12_12 265998687433 214074416447 194526752133
      (by decide) p (plane_0_3_11_sound p h0) (plane_2_10_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_0_3_11 plane_3_13_16 7119365177 26251808648 27443859744
      (by decide) p (plane_0_3_6_sound p h0) (plane_0_3_11_sound p h0) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_2_10_18 plane_3_14_16 526217738354 3481536161 248740136971
      (by decide) p (plane_0_3_11_sound p h0) (plane_2_10_18_sound p h2) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_3_15_15 plane_3_15_17 565595488056 48098237513 249168225957
      (by decide) p (plane_0_3_11_sound p h0) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_3_5_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 3)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 3 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 15 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_2_15_13 plane_2_15_15 plane_3_0_8 677744907 94191446894 94908832430
      (by decide) p (plane_2_15_13_sound p h2) (plane_2_15_15_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_13 plane_2_15_15 plane_3_1_9 4222434513 564918656176 569452994580
      (by decide) p (plane_2_15_13_sound p h2) (plane_2_15_15_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_13 plane_2_15_15 plane_3_2_10 179026671 294976028962 284726497290
      (by decide) p (plane_2_15_13_sound p h2) (plane_2_15_15_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_15 plane_2_15_17 plane_3_3_14 51246234389 10737139835 23566478669
      (by decide) p (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2) (plane_3_3_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_5 plane_2_15_15 plane_3_4_12 4445101833 282458329541 286092288567
      (by decide) p (plane_1_5_5_sound p h1) (plane_2_15_15_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_13 plane_2_15_15 plane_3_5_13 4460421057 283820556874 284726497290
      (by decide) p (plane_2_15_13_sound p h2) (plane_2_15_15_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_13 plane_2_15_15 plane_3_6_14 4460421057 283820556874 284726497290
      (by decide) p (plane_2_15_13_sound p h2) (plane_2_15_15_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_15 plane_2_15_17 plane_3_7_17 366465071157 188376034105 188531829352
      (by decide) p (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(39 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row39]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_15_13 plane_2_15_15 plane_3_9_17 179026671 294976028962 284726497290
      (by decide) p (plane_2_15_13_sound p h2) (plane_2_15_15_sound p h2) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_2_15_15 plane_3_10_17 282121243926 188718161132 248783313891
      (by decide) p (plane_0_3_11_sound p h0) (plane_2_15_15_sound p h2) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_15_17 plane_3_11_13 plane_3_11_19 284726497290 282753367353 22752306341
      (by decide) p (plane_2_15_17_sound p h2) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_1_5_4 plane_3_12_12 194526752133 214074416447 265998687433
      (by decide) p (plane_0_3_11_sound p h0) (plane_1_5_4_sound p h1) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_0_3_11 plane_3_13_16 7119365177 26251808648 27443859744
      (by decide) p (plane_0_3_6_sound p h0) (plane_0_3_11_sound p h0) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_1_5_8 plane_3_14_16 507894424486 3481536161 240683185084
      (by decide) p (plane_0_3_11_sound p h0) (plane_1_5_8_sound p h1) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_8 plane_2_15_17 plane_3_15_17 2468704435 56478747583 56887120403
      (by decide) p (plane_1_5_8_sound p h1) (plane_2_15_17_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_3_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 3)
    (e1 : labels 1 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 3 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_2_2_10 plane_2_2_11 284027168089 539379949393 3015872044
      (by decide) p (plane_1_0_6_sound p h1) (plane_2_2_10_sound p h2) (plane_2_2_11_sound p h2))
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
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_1_0_9 plane_2_10_19 153753283400 194526752133 265998687433
      (by decide) p (plane_0_3_11_sound p h0) (plane_1_0_9_sound p h1) (plane_2_10_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_1_0_5 plane_2_11_19 30493944443 13408722488 39890497256
      (by decide) p (plane_0_3_6_sound p h0) (plane_1_0_5_sound p h1) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_2_12_18 65045933361 1039767016309 565595488056
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_13_13 plane_2_13_19 146561981297 2565962934 74160944991
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_1 plane_0_3_11 plane_2_14_19 108426769676000000 268211 232722
      (by decide) p (plane_0_3_1_sound p h0) (plane_0_3_11_sound p h0) (plane_2_14_19_sound p h2))
  · exact complete_3_0_15 labels p h e0 e1 he

theorem complete_3_1 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 3)
    (e1 : labels 1 = 1)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 3 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 1 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_1_1_15 plane_2_0_6 1094452375015 10571859773 564756396848
      (by decide) p (plane_1_1_9_sound p h1) (plane_1_1_15_sound p h1) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_1_9 plane_2_1_9 286058466951 57265570853 526217738354
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_1_9_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_1_9 plane_2_2_10 26964628053 6070146065 47837976214
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_1_9_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_1_9 plane_2_3_11 249154618709 103200090415 526217738354
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_1_9_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_4_4 plane_2_4_10 569452994580 21090479789 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_1_9 plane_2_5_15 155489854802 550574971302 263108869177
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_1_9_sound p h1) (plane_2_5_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_1_9 plane_2_6_15 18049170435 50671807899 47837976214
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_1_9_sound p h1) (plane_2_6_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_1_9 plane_2_7_15 282557077259 72410295677 526217738354
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_1_9_sound p h1) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_8_4 plane_2_8_14 1104672086663 28422632345 568649365826
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_9_9 plane_2_9_15 577364467412 21090479789 289889229815
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_4 plane_1_1_9 plane_2_10_15 91348355030 257015383608 286195087637
      (by decide) p (plane_1_1_4_sound p h1) (plane_1_1_9_sound p h1) (plane_2_10_15_sound p h2))
  · exact complete_3_1_11 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_12_12 plane_2_12_18 452528907170 65326480587 249154618709
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_13_13 plane_2_13_19 586247925188 10571859773 296610908583
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_4 plane_1_1_9 plane_2_14_19 91314533414 257182683523 286195087637
      (by decide) p (plane_1_1_4_sound p h1) (plane_1_1_9_sound p h1) (plane_2_14_19_sound p h2))
  · exact complete_3_1_15 labels p h e0 e1 he

theorem complete_3_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 3)
    (e1 : labels 1 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 3 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_3_16 plane_2_0_6 plane_2_0_8 94265914676 142571987185 254571102501
      (by decide) p (plane_0_3_16_sound p h0) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_5_13 plane_2_1_9 289889229815 57265570853 532335567341
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_5_13_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_5_13 plane_2_2_10 300648190012 66771606715 532335567341
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_5_13_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_5_13 plane_2_3_11 252961440741 103200090415 532335567341
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_5_13_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_14 plane_2_4_10 plane_2_4_12 561792632189 611492713598 467331756560
      (by decide) p (plane_0_3_14_sound p h0) (plane_2_4_10_sound p h2) (plane_2_4_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_5_13 plane_2_5_13 15457684384 2605024337 28017661439
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_5_13_sound p h1) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_2_6_14 plane_2_6_15 48064530945 36057965052 7487938076
      (by decide) p (plane_0_3_6_sound p h0) (plane_2_6_14_sound p h2) (plane_2_6_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_5_13 plane_2_7_15 286480696885 72410295677 532335567341
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_5_13_sound p h1) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_14 plane_2_8_14 plane_2_8_16 240757767921 259956015911 219653794147
      (by decide) p (plane_0_3_14_sound p h0) (plane_2_8_14_sound p h2) (plane_2_8_16_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_2_9_15 plane_2_9_17 73763178964 4794473669 61434141449
      (by decide) p (plane_0_3_6_sound p h0) (plane_2_9_15_sound p h2) (plane_2_9_17_sound p h2))
  · exact complete_3_5_10 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_1_5_5 plane_2_11_19 286092288567 40226167464 248405159872
      (by decide) p (plane_0_3_6_sound p h0) (plane_1_5_5_sound p h1) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_2_12_12 plane_2_12_18 90505781434 20640018083 43840363565
      (by decide) p (plane_0_3_11_sound p h0) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_2_13_13 plane_2_13_19 586247925188 58966354913 258269678195
      (by decide) p (plane_0_3_11_sound p h0) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_1_5_4 plane_2_14_14 194743933537 248740136971 265998687433
      (by decide) p (plane_0_3_11_sound p h0) (plane_1_5_4_sound p h1) (plane_2_14_14_sound p h2))
  · exact complete_3_5_15 labels p h e0 e1 he

theorem complete_3 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 3)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 3 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact complete_3_0 labels p h e0 he
  · exact complete_3_1 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_2_5 plane_1_2_10 288212352061 546434044369 243345192892
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_2_5_sound p h1) (plane_1_2_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_0_3_11 plane_1_3_5 232067096651 112850766838 226264453585
      (by decide) p (plane_0_3_5_sound p h0) (plane_0_3_11_sound p h0) (plane_1_3_5_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_1_4_4 plane_1_4_9 286122431238 240683185084 25315502349
      (by decide) p (plane_0_3_11_sound p h0) (plane_1_4_4_sound p h1) (plane_1_4_9_sound p h1))
  · exact complete_3_5 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_1_6_6 plane_1_6_8 73763178964 7752048309 32125196257
      (by decide) p (plane_0_3_6_sound p h0) (plane_1_6_6_sound p h1) (plane_1_6_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_0_3_11 plane_1_7_6 129701549796 223245267043 226264453585
      (by decide) p (plane_0_3_5_sound p h0) (plane_0_3_11_sound p h0) (plane_1_7_6_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_1_8_8 plane_1_8_14 274239687916 243045670659 16179247621
      (by decide) p (plane_0_3_11_sound p h0) (plane_1_8_8_sound p h1) (plane_1_8_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_3_6 plane_0_3_11 plane_1_9_9 21478273037 252386414120 219550877952
      (by decide) p (plane_0_3_6_sound p h0) (plane_0_3_11_sound p h0) (plane_1_9_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_0_3_11 plane_1_10_10 21478273037 532335567341 452528907170
      (by decide) p (plane_0_3_5_sound p h0) (plane_0_3_11_sound p h0) (plane_1_10_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_3_5 plane_1_11_13 plane_1_11_19 569452994580 526311269997 152783593819
      (by decide) p (plane_0_3_5_sound p h0) (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_0_3_16 plane_1_12_12 75018590869 5891706513 95129815937
      (by decide) p (plane_0_3_11_sound p h0) (plane_0_3_16_sound p h0) (plane_1_12_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_0_3_16 plane_1_13_13 805666748654 29600136713 761038527496
      (by decide) p (plane_0_3_11_sound p h0) (plane_0_3_16_sound p h0) (plane_1_13_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_3_11 plane_0_3_16 plane_1_14_14 98574973559 3147063011 95129815937
      (by decide) p (plane_0_3_11_sound p h0) (plane_0_3_16_sound p h0) (plane_1_14_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_3_16 plane_1_15_15 plane_1_15_17 94265914676 277114606429 131370843425
      (by decide) p (plane_0_3_16_sound p h0) (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_3
