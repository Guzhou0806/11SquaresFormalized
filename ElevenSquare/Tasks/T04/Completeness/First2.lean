import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 2.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_2_0_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 0)
    (e2 : labels 2 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 0 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 11 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_2_2 plane_1_0_6 plane_3_0_8 8906214456000000 534921 1057261
      (by decide) p (plane_0_2_2_sound p h0) (plane_1_0_6_sound p h1) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_3_1_8 plane_3_1_9 286038658844 1917121227 562870354603
      (by decide) p (plane_1_0_6_sound p h1) (plane_3_1_8_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_3_2_4 plane_3_2_10 293123962594 4966236753 558968563873
      (by decide) p (plane_1_0_6_sound p h1) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_3_3_16 142571987185 254571102501 94265914676
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_2 plane_1_0_6 plane_3_4_12 75681430772000000 528190 1057261
      (by decide) p (plane_0_2_2_sound p h0) (plane_1_0_6_sound p h1) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_3_5_13 145011768897 3615241625 282797744028
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_11_19 plane_3_6_8 94869191801 2115090599 47687671440
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_11_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_3_7_17 188807480585 365596738813 188531829352
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_3_7_17_sound p h3))
  · refine ⟨(20 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row20]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_0_9 plane_3_9_12 plane_3_9_17 40575309727 28769887088 30598113403
      (by decide) p (plane_1_0_9_sound p h1) (plane_3_9_12_sound p h3) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_3_10_17 94168568283 275461549151 282797744028
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_3_11_13 plane_3_11_19 94908832430 47692487307 2115090599
      (by decide) p (plane_1_0_8_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_11_19 plane_3_12_12 8438500783 82927771297 95375342880
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_11_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_14 plane_2_11_19 plane_3_13_12 273727962933 121004392604 286122431238
      (by decide) p (plane_2_11_14_sound p h2) (plane_2_11_19_sound p h2) (plane_3_13_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_11_19 plane_3_14_16 175437089999 19186699841 95375342880
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_11_19_sound p h2) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_11_19 plane_3_15_17 31417040817 123697423 15895890480
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_11_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_2_0_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 0)
    (e2 : labels 2 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_2_2 plane_2_15_15 plane_3_4_12 17780407332000000 528190 534921
      (by decide) p (plane_0_2_2_sound p h0) (plane_2_15_15_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_5_13 1486807019 48337256299 47687671440
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_6_14 1486807019 48337256299 47687671440
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_15_15 plane_3_7_17 37675206821 37761496117 19075068576
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_15_15_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(21 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row21]
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
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_3_12_12 plane_3_12_17 27443859744 26251808648 7119365177
      (by decide) p (plane_0_2_7_sound p h0) (plane_3_12_12_sound p h3) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_2_15_14 plane_3_13_16 16091708513 26251808648 27631156413
      (by decide) p (plane_0_2_7_sound p h0) (plane_2_15_14_sound p h2) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_1_0_8 plane_3_14_16 57560099523 465031791928 248412460584
      (by decide) p (plane_0_2_7_sound p h0) (plane_1_0_8_sound p h1) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_1_0_8 plane_3_15_17 1113276807 245640855940 124206230292
      (by decide) p (plane_0_2_7_sound p h0) (plane_1_0_8_sound p h1) (plane_3_15_17_sound p h3))

theorem complete_2_1_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 1)
    (e2 : labels 2 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 1 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 11 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_2_2 plane_2_11_11 plane_3_0_8 17780407332000000 534921 528190
      (by decide) p (plane_0_2_2_sound p h0) (plane_2_11_11_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_11 plane_3_1_8 plane_3_1_9 143019329422 2145067255 138389323997
      (by decide) p (plane_2_11_11_sound p h2) (plane_3_1_8_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_11 plane_3_2_12 541387309342 566664611867 282557077259
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_11_sound p h2) (plane_3_2_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_19 plane_3_3_5 526311269997 57265570853 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(22 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row22]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_11 plane_3_5_8 281068782504 95737115210 282557077259
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_11_sound p h2) (plane_3_5_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_19 plane_3_6_8 569215150806 12377849851 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_11 plane_3_7_17 541387309342 566664611867 282557077259
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_11_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(23 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row23]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_11 plane_3_9_12 268090853421 88201229486 282557077259
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_11_sound p h2) (plane_3_9_12_sound p h3))
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

theorem complete_2_1_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 1)
    (e2 : labels 2 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_2_2 plane_2_15_15 plane_3_4_12 17780407332000000 528190 534921
      (by decide) p (plane_0_2_2_sound p h0) (plane_2_15_15_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_5_13 8920842114 289994215265 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_3_6_8 plane_3_6_14 577364467412 289994215265 12377849851
      (by decide) p (plane_1_1_9_sound p h1) (plane_3_6_8_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_7_17 565128102315 566664611867 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(24 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row24]
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
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_1_1_9 plane_3_12_12 248740136971 56954921416 248405159872
      (by decide) p (plane_0_2_7_sound p h0) (plane_1_1_9_sound p h1) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_15_15 plane_3_13_16 248412460584 40357234280 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_15_15_sound p h2) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_4 plane_1_1_9 plane_3_14_16 57265570853 508188953156 286195087637
      (by decide) p (plane_1_1_4_sound p h1) (plane_1_1_9_sound p h1) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_1_1_9 plane_3_15_17 1917121227 491281711880 248405159872
      (by decide) p (plane_0_2_7_sound p h0) (plane_1_1_9_sound p h1) (plane_3_15_17_sound p h3))

theorem complete_2_2_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 2)
    (e2 : labels 2 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 11 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_2_2 plane_2_11_11 plane_3_0_8 17780407332000000 534921 528190
      (by decide) p (plane_0_2_2_sound p h0) (plane_2_11_11_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_11 plane_3_1_8 plane_3_1_9 143019329422 2145067255 138389323997
      (by decide) p (plane_2_11_11_sound p h2) (plane_3_1_8_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_11 plane_3_2_10 plane_3_2_12 585143809623 541387309342 8417041069
      (by decide) p (plane_2_11_11_sound p h2) (plane_3_2_10_sound p h3) (plane_3_2_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_11_19 plane_3_3_5 526311269997 66771606715 296643779964
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_11_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(25 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row25]
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
  · exact False.elim (refutationCheck_sound plane_1_2_5 plane_1_2_9 plane_3_8_8 177664844544 104793484997 279339316598
      (by decide) p (plane_1_2_5_sound p h1) (plane_1_2_9_sound p h1) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_9 plane_1_2_9 plane_3_9_8 8154722029 22367449111 20318017992
      (by decide) p (plane_0_2_9_sound p h0) (plane_1_2_9_sound p h1) (plane_3_9_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_3_10_10 plane_3_10_17 140046111449 97445420627 150324095006
      (by decide) p (plane_0_2_10_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_3_11_13 plane_3_11_19 284726497290 148309456911 10415553607
      (by decide) p (plane_1_2_10_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_1_2_4 plane_3_12_12 58966354913 257938437109 586324303038
      (by decide) p (plane_0_2_10_sound p h0) (plane_1_2_4_sound p h1) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_1_2_4 plane_3_13_13 1655412251 51249358108 97720717173
      (by decide) p (plane_0_2_10_sound p h0) (plane_1_2_4_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_11_19 plane_3_14_16 175437089999 20109858339 98872971274
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_11_19_sound p h2) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_11_19 plane_3_15_17 282753367353 1507936022 148309456911
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_11_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_2_5_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 6 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_0_2_10 plane_3_0_8 74160944991 2565962934 146561981297
      (by decide) p (plane_0_2_4_sound p h0) (plane_0_2_10_sound p h0) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_6_6 plane_3_1_9 520176509 296610908583 307517547530
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_6_6_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_3_2_4 plane_3_2_10 146561981297 76874037162 753968011
      (by decide) p (plane_0_2_10_sound p h0) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_6_14 plane_3_3_5 532335567341 60329575017 300564288862
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_6_14_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_9 plane_2_6_15 plane_3_4_13 21350669565 22367449111 8154722029
      (by decide) p (plane_0_2_9_sound p h0) (plane_2_6_15_sound p h2) (plane_3_4_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_9 plane_3_5_8 plane_3_5_13 16021510315 10117034367 12250414744
      (by decide) p (plane_0_2_9_sound p h0) (plane_3_5_8_sound p h3) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_3_6_8 plane_3_6_14 144341116853 75162047503 3467060182
      (by decide) p (plane_0_2_10_sound p h0) (plane_3_6_8_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_3_7_9 plane_3_7_19 1104672086663 589503107161 21657103543
      (by decide) p (plane_0_2_10_sound p h0) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_15 plane_3_8_8 plane_3_8_13 30219441171 11497565201 31203773929
      (by decide) p (plane_2_6_15_sound p h2) (plane_3_8_8_sound p h3) (plane_3_8_13_sound p h3))
  · refine ⟨(26 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row26]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_3_10_10 plane_3_10_17 140046111449 97445420627 150324095006
      (by decide) p (plane_0_2_10_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_3_11_13 plane_3_11_19 142363248645 74160944991 3467060182
      (by decide) p (plane_0_2_10_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_6_14 plane_3_12_12 21478273037 257938437109 300564288862
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_6_14_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_5 plane_2_6_14 plane_3_13_13 5338712606 296584132177 289889229815
      (by decide) p (plane_1_5_5_sound p h1) (plane_2_6_14_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_5 plane_2_6_14 plane_3_14_14 9078349777 286091972249 289889229815
      (by decide) p (plane_1_5_5_sound p h1) (plane_2_6_14_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_6_14 plane_3_15_17 286489913177 1507936022 150282144431
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_6_14_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_2_5_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 10 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_10_10 plane_3_0_8 4460421057 148321889982 150282144431
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_10_10_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_10_10 plane_3_1_9 9078349777 296610908583 300564288862
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_10_10_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_10_10 plane_3_2_10 157020959 9044004372 8840126143
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_10_10_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_10_10 plane_3_3_16 406521813347 442908082269 150282144431
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_10_10_sound p h2) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_10_10 plane_3_4_12 234817143 292859327197 300564288862
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_10_10_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_10_10 plane_3_5_13 365910075 7911794474 7909586549
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_10_10_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_10_18 plane_3_6_8 569141090689 13868240728 296584132177
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_10_18_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_10_10 plane_3_7_17 582135485611 586487235117 300564288862
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_10_10_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(27 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row27]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(28 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row28]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_10_10 plane_3_10_17 144513751499 97445420627 150282144431
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_10_10_sound p h2) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_3_11_13 plane_3_11_19 142363248645 74160944991 3467060182
      (by decide) p (plane_0_2_10_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_3_12_12 plane_3_12_17 27443859744 26251808648 7119365177
      (by decide) p (plane_0_2_7_sound p h0) (plane_3_12_12_sound p h3) (plane_3_12_17_sound p h3))
  · refine ⟨(29 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row29]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_10_18 plane_3_14_16 526217738354 60329575017 296584132177
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_10_18_sound p h2) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_10_18 plane_3_15_17 565438832685 3015872044 296584132177
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_10_18_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_2_5_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_11_19 plane_3_3_5 175437089999 20109858339 98872971274
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_11_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(30 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row30]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_11_10 plane_3_5_8 plane_3_5_13 3204302063 3099650918 1170482995
      (by decide) p (plane_2_11_10_sound p h2) (plane_3_5_8_sound p h3) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_11_19 plane_3_6_8 284607575403 6934120364 148309456911
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_11_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_11_11 plane_3_7_17 541387309342 586487235117 292938243343
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_11_11_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(31 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row31]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(32 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row32]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_3_10_10 plane_3_10_17 140046111449 97445420627 150324095006
      (by decide) p (plane_0_2_10_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_3_11_13 plane_3_11_19 142363248645 74160944991 3467060182
      (by decide) p (plane_0_2_10_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_11_19 plane_3_12_12 25315502349 257938437109 296618913822
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_11_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_14 plane_2_11_19 plane_3_13_12 273727962933 121004392604 286122431238
      (by decide) p (plane_2_11_14_sound p h2) (plane_2_11_19_sound p h2) (plane_3_13_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_5 plane_2_11_19 plane_3_14_14 4222434513 286091972249 286092288567
      (by decide) p (plane_1_5_5_sound p h1) (plane_2_11_19_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_11_19 plane_3_15_17 282753367353 1507936022 148309456911
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_11_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_2_5_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 15 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_15_15 plane_3_0_8 96820701 7062947142 7062355091
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_15_15_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_15_15 plane_3_1_9 11632051 817109941 817131994
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_15_15_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_15_15 plane_3_2_10 59675557 51249358108 49436485637
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_15_15_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_15_15 plane_3_3_14 42948559340 108255805162 49436485637
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_15_15_sound p h2) (plane_3_3_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_5 plane_2_15_15 plane_3_4_12 4445101833 282458329541 286092288567
      (by decide) p (plane_1_5_5_sound p h1) (plane_2_15_15_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_15_15 plane_3_5_13 4460421057 150324095006 148309456911
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_15_15_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_15_15 plane_3_6_14 4460421057 150324095006 148309456911
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_15_15_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_15_15 plane_3_7_17 26910862015 27927963577 14124710182
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_15_15_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(33 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row33]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_15_15 plane_3_9_17 59675557 51249358108 49436485637
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_15_15_sound p h2) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_15_15 plane_3_10_17 141060621963 97445420627 148309456911
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_15_15_sound p h2) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_3_11_13 plane_3_11_19 142363248645 74160944991 3467060182
      (by decide) p (plane_0_2_10_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_3_12_12 plane_3_12_17 27443859744 26251808648 7119365177
      (by decide) p (plane_0_2_7_sound p h0) (plane_3_12_12_sound p h3) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_2_15_14 plane_3_13_16 16091708513 26251808648 27631156413
      (by decide) p (plane_0_2_7_sound p h0) (plane_2_15_14_sound p h2) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_0_2_10 plane_3_14_16 2080330173 16035579032 8878343656
      (by decide) p (plane_0_2_7_sound p h0) (plane_0_2_10_sound p h0) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_0_2_10 plane_3_15_17 753968011 122820427970 64367991506
      (by decide) p (plane_0_2_7_sound p h0) (plane_0_2_10_sound p h0) (plane_3_15_17_sound p h3))

theorem complete_2_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_1_0_9 plane_2_10_19 19219160425 27631156413 16091708513
      (by decide) p (plane_0_2_7_sound p h0) (plane_1_0_9_sound p h1) (plane_2_10_19_sound p h2))
  · exact complete_2_0_11 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_0_6 plane_1_0_8 plane_2_12_18 65045933361 1039767016309 565595488056
      (by decide) p (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_0_8 plane_2_13_13 plane_2_13_19 146561981297 2565962934 74160944991
      (by decide) p (plane_1_0_8_sound p h1) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_7 plane_1_0_8 plane_2_14_14 286092288567 40357234280 248412460584
      (by decide) p (plane_0_2_7_sound p h0) (plane_1_0_8_sound p h1) (plane_2_14_14_sound p h2))
  · exact complete_2_0_15 labels p h e0 e1 he

theorem complete_2_1 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 1)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 1 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_1_9 plane_2_0_6 10571859773 1117937127746 565438832685
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_1_9_sound p h1) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_1_9 plane_2_1_15 119407635311 224065937123 113087766537
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_1_9_sound p h1) (plane_2_1_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_1_9 plane_2_2_10 98870302861 3310824502 188479610895
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_1_9_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_1_9 plane_2_3_11 249154618709 58966354913 565438832685
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_1_9_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_4_4 plane_2_4_10 569452994580 21090479789 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_1_9 plane_2_5_11 5684526469 219898441339 113087766537
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_1_9_sound p h1) (plane_2_5_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_6_11 plane_2_6_15 271974970539 198540874785 84016202474
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_6_11_sound p h2) (plane_2_6_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_5 plane_1_1_6 plane_2_7_15 92227723283 104793484997 194279197068
      (by decide) p (plane_0_2_5_sound p h0) (plane_1_1_6_sound p h1) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_8_4 plane_2_8_14 1104672086663 28422632345 568649365826
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_9_9 plane_2_9_15 577364467412 21090479789 289889229815
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_4 plane_1_1_9 plane_2_10_15 91348355030 257015383608 286195087637
      (by decide) p (plane_1_1_4_sound p h1) (plane_1_1_9_sound p h1) (plane_2_10_15_sound p h2))
  · exact complete_2_1_11 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_1_9 plane_2_12_18 7258497843 115826997001 62826536965
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_1_9_sound p h1) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_13_13 plane_2_13_19 586247925188 10571859773 296610908583
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_4 plane_1_1_9 plane_2_14_19 91314533414 257182683523 286195087637
      (by decide) p (plane_1_1_4_sound p h1) (plane_1_1_9_sound p h1) (plane_2_14_19_sound p h2))
  · exact complete_2_1_15 labels p h e0 e1 he

theorem complete_2_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_2_10 plane_2_0_6 1507936022 558968563873 293162151519
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_2_10_sound p h1) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_2_10 plane_2_1_9 98870302861 639040409 195441434346
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_2_10_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_2_10 plane_2_2_10 51249358108 1655412251 97720717173
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_2_10_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_2_10 plane_2_3_11 257938437109 58966354913 586324303038
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_2_10_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_4_4 plane_2_4_10 142363248645 3467060182 74160944991
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_2_10 plane_2_5_11 21657103543 1099492206695 586324303038
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_2_10_sound p h1) (plane_2_5_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_9 plane_1_2_9 plane_2_6_15 22367449111 8154722029 20318017992
      (by decide) p (plane_0_2_9_sound p h0) (plane_1_2_9_sound p h1) (plane_2_6_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_5 plane_0_2_9 plane_2_7_15 177664844544 104793484997 279339316598
      (by decide) p (plane_0_2_5_sound p h0) (plane_0_2_9_sound p h0) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_8_4 plane_2_8_14 1104672086663 21657103543 589503107161
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_10 plane_2_9_9 plane_2_9_15 144341116853 3467060182 75162047503
      (by decide) p (plane_1_2_10_sound p h1) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_2_9 plane_2_10_10 plane_2_10_15 16021510315 12250414744 10117034367
      (by decide) p (plane_1_2_9_sound p h1) (plane_2_10_10_sound p h2) (plane_2_10_15_sound p h2))
  · exact complete_2_2_11 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_1_2_10 plane_2_12_18 6703286113 115826997001 65147144782
      (by decide) p (plane_0_2_4_sound p h0) (plane_1_2_10_sound p h1) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_13_13 plane_2_13_19 293123962594 4966236753 153758773765
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_1_2_4 plane_2_14_14 10571859773 296584132177 586324303038
      (by decide) p (plane_0_2_10_sound p h0) (plane_1_2_4_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_1_2_4 plane_2_15_15 1710641956 49436485637 97720717173
      (by decide) p (plane_0_2_10_sound p h0) (plane_1_2_4_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_2_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    (e1 : labels 1 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_0_2_10 plane_2_0_6 4966236753 558968563873 293123962594
      (by decide) p (plane_0_2_4_sound p h0) (plane_0_2_10_sound p h0) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_0_2_10 plane_2_1_9 296584132177 1917121227 586247925188
      (by decide) p (plane_0_2_4_sound p h0) (plane_0_2_10_sound p h0) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_0_2_10 plane_2_2_10 153758773765 4966236753 293123962594
      (by decide) p (plane_0_2_4_sound p h0) (plane_0_2_10_sound p h0) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_0_2_10 plane_2_3_11 258269678195 58966354913 586247925188
      (by decide) p (plane_0_2_4_sound p h0) (plane_0_2_10_sound p h0) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_4_4 plane_2_4_10 284726497290 10415553607 148309456911
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_0_2_10 plane_2_5_11 28457152733 1099492206695 586247925188
      (by decide) p (plane_0_2_4_sound p h0) (plane_0_2_10_sound p h0) (plane_2_5_11_sound p h2))
  · exact complete_2_5_6 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_2_9 plane_1_5_6 plane_2_7_15 7930389749 7402701856 15238513494
      (by decide) p (plane_0_2_9_sound p h0) (plane_1_5_6_sound p h1) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_8_4 plane_2_8_14 1104672086663 28457152733 589557157165
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_9_9 plane_2_9_15 288682233706 10415553607 150282144431
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact complete_2_5_10 labels p h e0 e1 he
  · exact complete_2_5_11 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_0_2_10 plane_2_12_18 66771606715 1042442973009 586247925188
      (by decide) p (plane_0_2_4_sound p h0) (plane_0_2_10_sound p h0) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_2_13_13 plane_2_13_19 293123962594 4966236753 153758773765
      (by decide) p (plane_0_2_10_sound p h0) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_1_5_4 plane_2_14_14 194743933537 296584132177 296371652216
      (by decide) p (plane_0_2_10_sound p h0) (plane_1_5_4_sound p h1) (plane_2_14_14_sound p h2))
  · exact complete_2_5_15 labels p h e0 e1 he

theorem complete_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 2 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact complete_2_0 labels p h e0 he
  · exact complete_2_1 labels p h e0 he
  · exact complete_2_2 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_2_5 plane_0_2_10 plane_1_3_5 546434044369 243345192892 288212352061
      (by decide) p (plane_0_2_5_sound p h0) (plane_0_2_10_sound p h0) (plane_1_3_5_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_2_11 plane_1_4_4 plane_1_4_9 286122431238 121004392604 273727962933
      (by decide) p (plane_0_2_11_sound p h0) (plane_1_4_4_sound p h1) (plane_1_4_9_sound p h1))
  · exact complete_2_5 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_2_9 plane_1_6_6 plane_1_6_9 146115791345 37885836517 144976325411
      (by decide) p (plane_0_2_9_sound p h0) (plane_1_6_6_sound p h1) (plane_1_6_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_0_2_10 plane_1_7_6 286601706769 422081433215 586247925188
      (by decide) p (plane_0_2_4_sound p h0) (plane_0_2_10_sound p h0) (plane_1_7_6_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_0_2_10 plane_1_8_4 8058987727 1124082257821 586247925188
      (by decide) p (plane_0_2_4_sound p h0) (plane_0_2_10_sound p h0) (plane_1_8_4_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_1_9_4 plane_1_9_9 146593533603 2669356303 145516469805
      (by decide) p (plane_0_2_10_sound p h0) (plane_1_9_4_sound p h1) (plane_1_9_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_1_10_10 plane_1_10_12 29686905845 30344966189 280984874
      (by decide) p (plane_0_2_10_sound p h0) (plane_1_10_10_sound p h1) (plane_1_10_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_0_2_10 plane_1_11_11 8417041069 558575523115 586247925188
      (by decide) p (plane_0_2_4_sound p h0) (plane_0_2_10_sound p h0) (plane_1_11_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_2_4 plane_0_2_10 plane_1_12_12 29600136713 492686929159 586247925188
      (by decide) p (plane_0_2_4_sound p h0) (plane_0_2_10_sound p h0) (plane_1_12_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_0_2_12 plane_1_13_13 578265315311 3627754886 585143809623
      (by decide) p (plane_0_2_10_sound p h0) (plane_0_2_12_sound p h0) (plane_1_13_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_1_14_14 plane_1_14_16 527155870326 546434044369 520176509
      (by decide) p (plane_0_2_10_sound p h0) (plane_1_14_14_sound p h1) (plane_1_14_16_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_2_10 plane_1_15_13 plane_1_15_15 284726497290 179026671 294976028962
      (by decide) p (plane_0_2_10_sound p h0) (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_2
