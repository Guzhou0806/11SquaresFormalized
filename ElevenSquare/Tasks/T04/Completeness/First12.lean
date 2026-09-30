import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 12.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_12_10_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 12)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 12 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 0 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_10_15 plane_2_0_6 plane_3_0_6 2468704435 56478747583 56887120403
      (by decide) p (plane_1_10_15_sound p h1) (plane_2_0_6_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_1_10_19 plane_3_1_7 565454524009 3481536161 265998687433
      (by decide) p (plane_0_12_12_sound p h0) (plane_1_10_19_sound p h1) (plane_3_1_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_0_12_17 plane_3_2_7 26251808648 7119365177 27443859744
      (by decide) p (plane_0_12_12_sound p h0) (plane_0_12_17_sound p h0) (plane_3_2_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_1_10_19 plane_3_3_11 194526752133 214074416447 265998687433
      (by decide) p (plane_0_12_12_sound p h0) (plane_1_10_19_sound p h1) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_3_4_4 plane_3_4_10 284726497290 22752306341 282753367353
      (by decide) p (plane_2_0_6_sound p h2) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_2_0_8 plane_3_5_6 282121243926 188718161132 248783313891
      (by decide) p (plane_0_12_12_sound p h0) (plane_2_0_8_sound p h2) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_10_18 plane_3_6_6 296584132177 41390492312 248405159872
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_10_18_sound p h1) (plane_3_6_6_sound p h3))
  · refine ⟨(180 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row180]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_2_0_8 plane_3_8_13 274086016275 164242869823 565595488056
      (by decide) p (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_2_0_8 plane_3_9_9 4460421057 286489913177 282797744028
      (by decide) p (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2) (plane_3_9_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_2_0_8 plane_3_10_10 4460421057 286489913177 282797744028
      (by decide) p (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_0_8 plane_3_11_11 4445101833 282458329541 286092288567
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_0_8_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_2_0_8 plane_3_12_7 131370843425 277114606429 94265914676
      (by decide) p (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2) (plane_3_12_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_2_0_8 plane_3_13_13 59675557 97720717173 94265914676
      (by decide) p (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_2_0_8 plane_3_14_14 1407478171 188479610895 188531829352
      (by decide) p (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_0_6 plane_2_0_8 plane_3_15_15 677744907 94251122451 94265914676
      (by decide) p (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_12_10_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 12)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 12 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_2_5_5 plane_3_1_7 526217738354 3481536161 248740136971
      (by decide) p (plane_0_12_12_sound p h0) (plane_2_5_5_sound p h2) (plane_3_1_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_0_12_17 plane_3_2_7 26251808648 7119365177 27443859744
      (by decide) p (plane_0_12_12_sound p h0) (plane_0_12_17_sound p h0) (plane_3_2_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_1_10_19 plane_3_3_11 194526752133 214074416447 265998687433
      (by decide) p (plane_0_12_12_sound p h0) (plane_1_10_19_sound p h1) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_3_4_5 plane_3_4_10 23403467649 100311146 11869003391
      (by decide) p (plane_1_10_10_sound p h1) (plane_3_4_5_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_0_12_14 plane_3_5_6 186330252726 94359080566 240757767921
      (by decide) p (plane_0_12_12_sound p h0) (plane_0_12_14_sound p h0) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_10_18 plane_3_6_6 296584132177 41390492312 248405159872
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_10_18_sound p h1) (plane_3_6_6_sound p h3))
  · refine ⟨(181 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row181]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_5_13 plane_3_8_13 14694915777 4938379633 15457684384
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_5_13_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_3_9_9 plane_3_9_15 288682233706 532786927221 107567862531
      (by decide) p (plane_0_12_14_sound p h0) (plane_3_9_9_sound p h3) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_10_18 plane_3_10_10 289994215265 33029106456 248405159872
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_10_18_sound p h1) (plane_3_10_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_10_18 plane_3_11_11 282458329541 233904112176 530596102314
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_10_18_sound p h1) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_10_10 plane_3_12_14 40083125477 133522064130 90235652853
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_10_10_sound p h1) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_5_13 plane_3_13_13 8264261 465269797 454637776
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_5_13_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_10_18 plane_3_14_14 286091972249 220731986364 530596102314
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_10_18_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_10_18 plane_3_15_15 95374467851 73682118402 176865367438
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_10_18_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_12_14_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 12)
    (e1 : labels 1 = 14)
    (e2 : labels 2 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 12 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 14 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 0 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_1_14_19 plane_3_0_6 565096908217 1917121227 286195087637
      (by decide) p (plane_1_14_14_sound p h1) (plane_1_14_19_sound p h1) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_1_14_19 plane_3_1_7 508188953156 57265570853 286195087637
      (by decide) p (plane_1_14_14_sound p h1) (plane_1_14_19_sound p h1) (plane_3_1_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_14_19 plane_3_2_7 32675810698 26251808648 14958936471
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_14_19_sound p h1) (plane_3_2_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_3 plane_1_14_19 plane_3_3_11 108426769676000000 232722 268211
      (by decide) p (plane_0_12_3_sound p h0) (plane_1_14_19_sound p h1) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_4_5 291674394735 381829087459 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_4_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_3_5_5 plane_3_5_11 556142498998 19913735575 286091972249
      (by decide) p (plane_1_14_14_sound p h1) (plane_3_5_5_sound p h3) (plane_3_5_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_6_11 274086016275 88201229486 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_6_11_sound p h3))
  · refine ⟨(182 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row182]
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
  · exact False.elim (refutationCheck_sound plane_0_12_3 plane_2_0_8 plane_3_11_11 17780407332000000 528190 534921
      (by decide) p (plane_0_12_3_sound p h0) (plane_2_0_8_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_12_7 788225060550 855761983118 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_12_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_13_13 358053342 296584132177 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_14_14 4222434513 286091972249 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_0_8 plane_3_15_15 1355489814 95374467851 95364096189
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_0_8_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_12_14_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 12)
    (e1 : labels 1 = 14)
    (e2 : labels 2 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 12 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_2_4_4 plane_3_2_7 31051557573 26251808648 5028270933
      (by decide) p (plane_0_12_17_sound p h0) (plane_2_4_4_sound p h2) (plane_3_2_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_4_4 plane_3_3_11 1489147197 14631772763 16828958151
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_4_4_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_3_4_5 plane_3_4_10 772314432417 12377849851 381829087459
      (by decide) p (plane_1_14_14_sound p h1) (plane_3_4_5_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_4_4 plane_3_5_11 555849206859 19913735575 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_4_4_sound p h2) (plane_3_5_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_14_14 plane_3_6_11 44100614743 218931814155 265298051157
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_14_14_sound p h1) (plane_3_6_11_sound p h3))
  · refine ⟨(183 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row183]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_4_12 plane_3_8_13 268090853421 88201229486 282557077259
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_4_12_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_3_9_9 plane_3_9_15 577364467412 12377849851 289994215265
      (by decide) p (plane_1_14_14_sound p h1) (plane_3_9_9_sound p h3) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_3_10_10 plane_3_10_11 91691309771 64183263944 11009702152
      (by decide) p (plane_0_12_17_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_3 plane_0_12_17 plane_3_11_11 17429903280000000 52819 46388
      (by decide) p (plane_0_12_3_sound p h0) (plane_0_12_17_sound p h0) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_14_14 plane_3_12_14 38137733566 133522064130 88432683719
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_14_14_sound p h1) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_4_12 plane_3_13_14 273061638778 188469167116 282557077259
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_4_12_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_0_12_18 plane_3_14_14 21775493529 73577328788 175718623442
      (by decide) p (plane_0_12_14_sound p h0) (plane_0_12_18_sound p h0) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_0_12_18 plane_3_15_15 21681977787 73682118402 175718623442
      (by decide) p (plane_0_12_14_sound p h0) (plane_0_12_18_sound p h0) (plane_3_15_15_sound p h3))

theorem complete_12_15_0 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 12)
    (e1 : labels 1 = 15)
    (e2 : labels 2 = 0)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 12 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 15 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 0 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_12_0 plane_1_15_15 plane_3_0_6 8906214456000000 1057261 534921
      (by decide) p (plane_0_12_0_sound p h0) (plane_1_15_15_sound p h1) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_0 plane_1_15_15 plane_3_1_7 230240398092000000 984719 534921
      (by decide) p (plane_0_12_0_sound p h0) (plane_1_15_15_sound p h1) (plane_3_1_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_0_12_17 plane_3_2_7 26251808648 7119365177 27443859744
      (by decide) p (plane_0_12_12_sound p h0) (plane_0_12_17_sound p h0) (plane_3_2_7_sound p h3))
  · refine ⟨(184 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row184]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_3_4_4 plane_3_4_10 94908832430 2115090599 47692487307
      (by decide) p (plane_1_15_15_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_5_6 47020207321 31389522761 47687671440
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_5_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_3_6_6 plane_3_6_11 284027168089 225578898288 41390492312
      (by decide) p (plane_0_12_17_sound p h0) (plane_3_6_6_sound p h3) (plane_3_6_11_sound p h3))
  · refine ⟨(185 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row185]
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
  · exact False.elim (refutationCheck_sound plane_0_12_3 plane_2_0_8 plane_3_11_11 17780407332000000 528190 534921
      (by decide) p (plane_0_12_3_sound p h0) (plane_2_0_8_sound p h2) (plane_3_11_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_12_7 26274168685 28514397437 9537534288
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_12_7_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_13_13 59675557 49436485637 47687671440
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_14_14 1407478171 95374467851 95375342880
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_0_8 plane_3_15_15 225914969 15897495769 15895890480
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_0_8_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_12_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 12)
    (e1 : labels 1 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 12 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact complete_12_10_0 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_1_10_19 plane_2_1_9 194743933537 248740136971 265998687433
      (by decide) p (plane_0_12_12_sound p h0) (plane_1_10_19_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_2_2_4 plane_2_2_10 586247925188 258269678195 58966354913
      (by decide) p (plane_0_12_12_sound p h0) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_0_12_17 plane_2_3_5 448551107512 103200090415 219550877952
      (by decide) p (plane_0_12_12_sound p h0) (plane_0_12_17_sound p h0) (plane_2_3_5_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_10_18 plane_2_4_4 286092288567 40226167464 248405159872
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_10_18_sound p h1) (plane_2_4_4_sound p h2))
  · exact complete_12_10_5 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_0_12_14 plane_2_6_8 1039276630350 68452719217 481515535842
      (by decide) p (plane_0_12_12_sound p h0) (plane_0_12_14_sound p h0) (plane_2_6_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_10_10 plane_2_7_6 73310778095 114456098412 180471305706
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_10_10_sound p h1) (plane_2_7_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_10_18 plane_2_8_8 282557077259 210048033864 530596102314
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_10_18_sound p h1) (plane_2_8_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_10_18 plane_2_9_9 289889229815 44927628456 248405159872
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_10_18_sound p h1) (plane_2_9_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_10_18 plane_2_10_10 289889229815 240498752862 530596102314
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_10_18_sound p h1) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_11_13 plane_2_11_19 47454416215 24160503512 2550867439
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_10_18 plane_2_12_12 249154618709 9979649336 248405159872
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_10_18_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_10_18 plane_2_13_13 98870302861 76604175154 176865367438
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_10_18_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_10_18 plane_2_14_14 95352822317 76275467132 176865367438
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_10_18_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_10_18 plane_2_15_15 286092288567 40226167464 248405159872
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_10_18_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_12_14 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 12)
    (e1 : labels 1 = 14)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 12 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 14 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact complete_12_14_0 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_14_19 plane_2_1_4 plane_2_1_9 286195087637 91314533414 257182683523
      (by decide) p (plane_1_14_19_sound p h1) (plane_2_1_4_sound p h2) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_2_4 plane_2_2_10 586247925188 296610908583 10571859773
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_14_14 plane_2_3_5 65326480587 448551107512 248405159872
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_14_14_sound p h1) (plane_2_3_5_sound p h2))
  · exact complete_12_14_4 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_14_14 plane_2_5_4 6715308053 7622387976 8565695168
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_14_14_sound p h1) (plane_2_5_4_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_14_14 plane_2_6_8 21090479789 1039276630350 530596102314
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_14_14_sound p h1) (plane_2_6_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_7_6 plane_2_7_19 543733002463 568649365826 212594706109
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_7_6_sound p h2) (plane_2_7_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_3 plane_0_12_17 plane_2_8_8 12953275728000000 52819 46388
      (by decide) p (plane_0_12_3_sound p h0) (plane_0_12_17_sound p h0) (plane_2_8_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_2_9_4 plane_2_9_9 48864511201 7487938076 29353603808
      (by decide) p (plane_0_12_17_sound p h0) (plane_2_9_4_sound p h2) (plane_2_9_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_2_10_10 plane_2_10_12 564051211055 478928692456 44927628456
      (by decide) p (plane_0_12_17_sound p h0) (plane_2_10_10_sound p h2) (plane_2_10_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_11_13 plane_2_11_19 569452994580 286092288567 21090479789
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_3 plane_0_12_17 plane_2_12_12 9979649336000000 116361 115970
      (by decide) p (plane_0_12_3_sound p h0) (plane_0_12_17_sound p h0) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_2_13_12 plane_2_13_13 284027168089 229812525462 343368295236
      (by decide) p (plane_0_12_14_sound p h0) (plane_2_13_12_sound p h2) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_2_14_14 plane_2_14_17 139669658299 218315607360 114413200698
      (by decide) p (plane_0_12_14_sound p h0) (plane_2_14_14_sound p h2) (plane_2_14_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_14_14 plane_2_15_17 10571859773 489602753480 248405159872
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_14_14_sound p h1) (plane_2_15_17_sound p h2))

theorem complete_12_15 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 12)
    (e1 : labels 1 = 15)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 12 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 15 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact complete_12_15_0 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_12_0 plane_0_12_12 plane_2_1_4 108426769676000000 268211 232722
      (by decide) p (plane_0_12_0_sound p h0) (plane_0_12_12_sound p h0) (plane_2_1_4_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_2_4 plane_2_2_10 146561981297 74160944991 2565962934
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_13 plane_1_15_15 plane_2_3_5 65045933361 979437441292 569452994580
      (by decide) p (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1) (plane_2_3_5_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_15_18 plane_2_4_4 30493944443 13408722488 39890497256
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_15_18_sound p h1) (plane_2_4_4_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_1_15_14 plane_2_5_4 153753283400 194526752133 265998687433
      (by decide) p (plane_0_12_12_sound p h0) (plane_1_15_14_sound p h1) (plane_2_5_4_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_13 plane_1_15_15 plane_2_6_8 1039080153 55552212773 28472649729
      (by decide) p (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1) (plane_2_6_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_2_7_6 plane_2_7_19 77676143209 81244543299 30352639179
      (by decide) p (plane_1_15_15_sound p h1) (plane_2_7_6_sound p h2) (plane_2_7_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_15_15 plane_1_15_17 plane_2_8_8 6587121193 282585774453 565595488056
      (by decide) p (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1) (plane_2_8_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_2_9_4 plane_2_9_9 48864511201 7487938076 29353603808
      (by decide) p (plane_0_12_17_sound p h0) (plane_2_9_4_sound p h2) (plane_2_9_9_sound p h2))
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

theorem complete_12 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 12)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 12 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_0_12_14 plane_1_0_8 176844568170 8438500783 160505178614
      (by decide) p (plane_0_12_12_sound p h0) (plane_0_12_14_sound p h0) (plane_1_0_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_12_8 plane_0_12_14 plane_1_1_9 88432683719 4911106433 168144286396
      (by decide) p (plane_0_12_8_sound p h0) (plane_0_12_14_sound p h0) (plane_1_1_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_1_2_4 plane_1_2_10 586247925188 29600136713 492686929159
      (by decide) p (plane_0_12_12_sound p h0) (plane_1_2_4_sound p h1) (plane_1_2_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_12_8 plane_0_12_14 plane_1_3_11 219478844607 39746073673 504432859188
      (by decide) p (plane_0_12_8_sound p h0) (plane_0_12_14_sound p h0) (plane_1_3_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_4_10 plane_1_4_12 561792632189 517211038026 416357496870
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_4_10_sound p h1) (plane_1_4_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_0_12_14 plane_1_5_13 541413917118 21478273037 481515535842
      (by decide) p (plane_0_12_12_sound p h0) (plane_0_12_14_sound p h0) (plane_1_5_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_12_8 plane_1_6_8 plane_1_6_14 288682233706 10621727947 529759512937
      (by decide) p (plane_0_12_8_sound p h0) (plane_1_6_8_sound p h1) (plane_1_6_14_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_0_12_14 plane_1_7_19 1047744742536 57673997591 481515535842
      (by decide) p (plane_0_12_12_sound p h0) (plane_0_12_14_sound p h0) (plane_1_7_19_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_1_8_14 plane_1_8_16 7295689937 6650874079 5941736633
      (by decide) p (plane_0_12_14_sound p h0) (plane_1_8_14_sound p h1) (plane_1_8_16_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_9_15 plane_1_9_17 73763178964 32125196257 7752048309
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_9_15_sound p h1) (plane_1_9_17_sound p h1))
  · exact complete_12_10 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_12_12 plane_1_11_13 plane_1_11_19 189817664860 8438500783 165657187841
      (by decide) p (plane_0_12_12_sound p h0) (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_12_14 plane_0_12_18 plane_1_12_18 112850766838 150258102339 263577935163
      (by decide) p (plane_0_12_14_sound p h0) (plane_0_12_18_sound p h0) (plane_1_12_18_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_12_17 plane_1_13_18 plane_1_13_19 191104724741 70605495944 49065995824
      (by decide) p (plane_0_12_17_sound p h0) (plane_1_13_18_sound p h1) (plane_1_13_19_sound p h1))
  · exact complete_12_14 labels p h e0 he
  · exact complete_12_15 labels p h e0 he

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_12
