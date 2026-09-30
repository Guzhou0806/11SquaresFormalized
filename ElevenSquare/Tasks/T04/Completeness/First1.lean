import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 1.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_1_1_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 1)
    (e1 : labels 1 = 1)
    (e2 : labels 2 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 1 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 1 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 7 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_1_2 plane_1_1_7 plane_3_0_8 230240398092000000 534921 984719
      (by decide) p (plane_0_1_2_sound p h0) (plane_1_1_7_sound p h1) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_7 plane_3_1_8 plane_3_1_9 286038658844 57265570853 450628853633
      (by decide) p (plane_1_1_7_sound p h1) (plane_3_1_8_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_3_2_4 plane_3_2_10 586247925188 296610908583 10571859773
      (by decide) p (plane_0_1_9_sound p h0) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_3_5 1047812442533 65326480587 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(12 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row12]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_1_7 plane_3_5_8 253947212243 45674177515 263108869177
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_1_7_sound p h1) (plane_3_5_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_6_8 1131762613157 21090479789 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_7_9 1105418740127 28422632345 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_7_15 plane_3_8_8 12743111940 282458329541 282557077259
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_7_15_sound p h2) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_6 plane_2_7_15 plane_3_9_12 268090853421 236248611580 92227723283
      (by decide) p (plane_1_1_6_sound p h1) (plane_2_7_15_sound p h2) (plane_3_9_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_3_10_10 plane_3_10_17 280092222898 188469167116 289994215265
      (by decide) p (plane_1_1_9_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_11_13 1131762613157 21090479789 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_7_19 plane_3_12_12 57673997591 248740136971 568649365826
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_7_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_7_15 plane_3_13_13 8417041069 296584132177 282557077259
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_7_15_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_7_19 plane_3_14_14 67699997 286091972249 568649365826
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_7_19_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_7_19 plane_3_15_17 1124082257821 1917121227 568649365826
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_7_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_1_1_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 1)
    (e1 : labels 1 = 1)
    (e2 : labels 2 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 1 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 1 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 11 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_1_2 plane_2_11_11 plane_3_0_8 17780407332000000 534921 528190
      (by decide) p (plane_0_1_2_sound p h0) (plane_2_11_11_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_11 plane_3_1_8 plane_3_1_9 143019329422 2145067255 138389323997
      (by decide) p (plane_2_11_11_sound p h2) (plane_3_1_8_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_11 plane_3_2_12 541387309342 558077506053 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_11_sound p h2) (plane_3_2_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_19 plane_3_3_5 175437089999 21775493529 95374467851
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(13 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row13]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_11 plane_3_5_8 281068782504 91348355030 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_11_sound p h2) (plane_3_5_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_19 plane_3_6_8 569215150806 21090479789 286123403553
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_11 plane_3_7_17 541387309342 558077506053 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_11_sound p h2) (plane_3_7_17_sound p h3))
  · refine ⟨(14 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row14]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_11 plane_3_9_12 268090853421 84016202474 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_11_sound p h2) (plane_3_9_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_3_10_10 plane_3_10_17 280092222898 188469167116 289994215265
      (by decide) p (plane_1_1_9_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_3_11_13 plane_3_11_19 569452994580 286092288567 21090479789
      (by decide) p (plane_0_1_9_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_19 plane_3_12_12 1489147197 14631772763 16828958151
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_3_13_13 plane_3_13_16 257471966024 40357234280 296584132177
      (by decide) p (plane_1_1_9_sound p h1) (plane_3_13_13_sound p h3) (plane_3_13_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_19 plane_3_14_16 526311269997 57265570853 286092288567
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_19_sound p h2) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_11_19 plane_3_15_17 188502244902 639040409 95364096189
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_11_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_1_2_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 1)
    (e1 : labels 1 = 2)
    (e2 : labels 2 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 1 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 7 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(15 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row15]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_7 plane_3_1_8 12676863588 22200401293 14631772763
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_7_sound p h2) (plane_3_1_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_3_2_4 plane_3_2_10 586247925188 296610908583 10571859773
      (by decide) p (plane_0_1_9_sound p h0) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_3_5 1047812442533 65326480587 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(16 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row16]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_7 plane_3_5_8 240683185084 91348355030 248740136971
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_7_sound p h2) (plane_3_5_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_6_8 1131762613157 21090479789 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_7_9 1105418740127 28422632345 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_15 plane_3_8_8 12743111940 282557077259 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_15_sound p h2) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_15 plane_3_9_8 280833965361 198540874785 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_15_sound p h2) (plane_3_9_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_3_10_10 plane_3_10_17 280092222898 184172073764 289889229815
      (by decide) p (plane_0_1_9_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_11_13 1131762613157 21090479789 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_12_12 57673997591 249154618709 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_15 plane_3_13_13 8417041069 296610908583 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_15_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_14_14 67699997 286058466951 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_15_17 1124082257821 10571859773 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_1_2_11 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 1)
    (e1 : labels 1 = 2)
    (e2 : labels 2 = 11)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 1 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 11 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_1_2 plane_2_11_11 plane_3_0_8 17780407332000000 534921 528190
      (by decide) p (plane_0_1_2_sound p h0) (plane_2_11_11_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_11_11 plane_3_1_8 plane_3_1_9 143019329422 2145067255 138389323997
      (by decide) p (plane_2_11_11_sound p h2) (plane_3_1_8_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_11 plane_3_2_12 541387309342 558077506053 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_11_sound p h2) (plane_3_2_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_19 plane_3_3_5 175437089999 21775493529 95374467851
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(17 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row17]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_11 plane_3_5_8 281068782504 91348355030 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_11_sound p h2) (plane_3_5_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_19 plane_3_6_8 569215150806 21090479789 286123403553
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_11 plane_3_7_17 541387309342 558077506053 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_11_sound p h2) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_6 plane_1_2_5 plane_3_8_8 104793484997 92227723283 194279197068
      (by decide) p (plane_0_1_6_sound p h0) (plane_1_2_5_sound p h1) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_11 plane_3_9_12 268090853421 84016202474 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_11_sound p h2) (plane_3_9_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_3_10_10 plane_3_10_17 280092222898 184172073764 289889229815
      (by decide) p (plane_0_1_9_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_3_11_13 plane_3_11_19 569452994580 286092288567 21090479789
      (by decide) p (plane_0_1_9_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_2_4 plane_3_12_12 58966354913 249154618709 565438832685
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_2_4_sound p h1) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_2_4 plane_3_13_13 3310824502 98870302861 188479610895
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_2_4_sound p h1) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_19 plane_3_14_16 175437089999 21775493529 95374467851
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_19_sound p h2) (plane_3_14_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_11_19 plane_3_15_17 565506734706 10571859773 286123403553
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_11_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_1_3_7 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 1)
    (e1 : labels 1 = 3)
    (e2 : labels 2 = 7)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 1 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 3 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 7 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · refine ⟨(18 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row18]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_7 plane_3_1_8 12676863588 22200401293 14631772763
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_7_sound p h2) (plane_3_1_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_3_2_4 plane_3_2_10 586247925188 296610908583 10571859773
      (by decide) p (plane_0_1_9_sound p h0) (plane_3_2_4_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_3_5 1047812442533 65326480587 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_3_5_sound p h3))
  · refine ⟨(19 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row19]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_7 plane_3_5_8 240683185084 91348355030 248740136971
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_7_sound p h2) (plane_3_5_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_6_8 1131762613157 21090479789 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_6_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_7_9 1105418740127 28422632345 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_7_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_3_5 plane_3_8_8 72410295677 282557077259 526217738354
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_3_5_sound p h1) (plane_3_8_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_3_6 plane_3_9_9 plane_3_9_12 91691309771 82910326544 14975876152
      (by decide) p (plane_1_3_6_sound p h1) (plane_3_9_9_sound p h3) (plane_3_9_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_3_10_10 plane_3_10_17 280092222898 184172073764 289889229815
      (by decide) p (plane_0_1_9_sound p h0) (plane_3_10_10_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_11_13 1131762613157 21090479789 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_12_12 57673997591 249154618709 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_15 plane_3_13_13 8417041069 296610908583 282458329541
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_15_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_14_14 67699997 286058466951 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_7_19 plane_3_15_17 1124082257821 10571859773 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_7_19_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_1_1 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 1)
    (e1 : labels 1 = 1)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 1 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 1 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_1_15 plane_2_0_6 1094452375015 1917121227 555684376952
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_1_15_sound p h1) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_1_7 plane_2_1_15 904403389313 588464037365 526217738354
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_1_7_sound p h1) (plane_2_1_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_7 plane_2_2_10 plane_2_2_11 284027168089 461550255767 60329575017
      (by decide) p (plane_1_1_7_sound p h1) (plane_2_2_10_sound p h2) (plane_2_2_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_2 plane_1_1_7 plane_2_3_11 13926144644000000 465444 984719
      (by decide) p (plane_0_1_2_sound p h0) (plane_1_1_7_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_4_4 plane_2_4_10 569452994580 12377849851 286123403553
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_5_5 plane_2_5_11 556142498998 19913735575 286091972249
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_5_5_sound p h2) (plane_2_5_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_6_11 plane_2_6_15 271974970539 194257100055 88201229486
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_6_11_sound p h2) (plane_2_6_15_sound p h2))
  · exact complete_1_1_7 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_8_4 plane_2_8_14 1104672086663 19913735575 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_9_9 plane_2_9_15 577364467412 12377849851 289994215265
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_7 plane_1_1_9 plane_2_10_15 45674177515 253947212243 263108869177
      (by decide) p (plane_0_1_7_sound p h0) (plane_1_1_9_sound p h1) (plane_2_10_15_sound p h2))
  · exact complete_1_1_11 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_12_12 plane_2_12_18 452528907170 65326480587 249154618709
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_1_9 plane_2_13_13 plane_2_13_19 586247925188 10571859773 296610908583
      (by decide) p (plane_1_1_9_sound p h1) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_7 plane_2_14_14 plane_2_14_19 286195087637 508188953156 57265570853
      (by decide) p (plane_0_1_7_sound p h0) (plane_2_14_14_sound p h2) (plane_2_14_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_2 plane_0_1_7 plane_2_15_15 230240398092000000 534921 984719
      (by decide) p (plane_0_1_2_sound p h0) (plane_0_1_7_sound p h0) (plane_2_15_15_sound p h2))

theorem complete_1_2 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 1)
    (e1 : labels 1 = 2)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 1 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 2 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_2_11 plane_2_0_6 539379949393 1917121227 273581663960
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_2_11_sound p h1) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_2_11 plane_2_1_7 461550255767 57265570853 273581663960
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_2_11_sound p h1) (plane_2_1_7_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_2_7 plane_2_2_11 266969390600 208382902691 248405159872
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_2_7_sound p h1) (plane_2_2_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_2_7 plane_2_3_11 56954921416 248740136971 248405159872
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_2_7_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_4_4 plane_2_4_10 569452994580 12377849851 286123403553
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_5_5 plane_2_5_11 556142498998 19913735575 286091972249
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_5_5_sound p h2) (plane_2_5_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_6_11 plane_2_6_15 271974970539 194257100055 88201229486
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_6_11_sound p h2) (plane_2_6_15_sound p h2))
  · exact complete_1_2_7 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_8_4 plane_2_8_14 1104672086663 19913735575 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_9_9 plane_2_9_15 577364467412 12377849851 289994215265
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_2_4 plane_2_10_15 113774240806 19147423042 113087766537
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_2_4_sound p h1) (plane_2_10_15_sound p h2))
  · exact complete_1_2_11 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_12_12 plane_2_12_18 452528907170 57265570853 248740136971
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_13_13 plane_2_13_19 586247925188 1917121227 296584132177
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_2_4 plane_2_14_14 10571859773 286091972249 565438832685
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_2_4_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_2_4 plane_2_15_15 3421283912 95374467851 188479610895
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_2_4_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_1_3 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 1)
    (e1 : labels 1 = 3)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 1 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 3 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_1_8 plane_0_1_9 plane_2_0_6 1917121227 562870354603 286038658844
      (by decide) p (plane_0_1_8_sound p h0) (plane_0_1_9_sound p h0) (plane_2_0_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_8 plane_0_1_9 plane_2_1_7 57265570853 450628853633 286038658844
      (by decide) p (plane_0_1_8_sound p h0) (plane_0_1_9_sound p h0) (plane_2_1_7_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_2_7 plane_2_2_10 257471966024 296584132177 40357234280
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_2_7_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_2 plane_0_1_4 plane_2_3_11 108426769676000000 232722 268211
      (by decide) p (plane_0_1_2_sound p h0) (plane_0_1_4_sound p h0) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_4_4 plane_2_4_10 569452994580 12377849851 286123403553
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_5_5 plane_2_5_11 556142498998 19913735575 286091972249
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_5_5_sound p h2) (plane_2_5_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_3_5 plane_2_6_11 260939915392 44100614743 263108869177
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_3_5_sound p h1) (plane_2_6_11_sound p h2))
  · exact complete_1_3_7 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_8_4 plane_2_8_14 1104672086663 19913735575 568581733094
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_9_9 plane_2_9_15 577364467412 12377849851 289994215265
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_9_9_sound p h2) (plane_2_9_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_3_5 plane_2_10_10 74753504753 289994215265 526217738354
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_3_5_sound p h1) (plane_2_10_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_2 plane_1_3_6 plane_2_11_11 17429903280000000 52819 46388
      (by decide) p (plane_0_1_2_sound p h0) (plane_1_3_6_sound p h1) (plane_2_11_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_12_12 plane_2_12_18 452528907170 57265570853 248740136971
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_2_13_13 plane_2_13_19 586247925188 1917121227 296584132177
      (by decide) p (plane_0_1_9_sound p h0) (plane_2_13_13_sound p h2) (plane_2_13_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_3_5 plane_2_14_14 65326480587 286091972249 526217738354
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_3_5_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_3_5 plane_2_15_15 65045933361 286123403553 526217738354
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_3_5_sound p h1) (plane_2_15_15_sound p h2))

theorem complete_1 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 1)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 1 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_1_7 plane_0_1_9 plane_1_0_5 287626254203 110684373445 527155870326
      (by decide) p (plane_0_1_7_sound p h0) (plane_0_1_9_sound p h0) (plane_1_0_5_sound p h1))
  · exact complete_1_1 labels p h e0 he
  · exact complete_1_2 labels p h e0 he
  · exact complete_1_3 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_1_7 plane_0_1_9 plane_1_4_4 8428013 1050521497 1052207326
      (by decide) p (plane_0_1_7_sound p h0) (plane_0_1_9_sound p h0) (plane_1_4_4_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_1_6 plane_0_1_9 plane_1_5_6 141095471221 41766690707 139669658299
      (by decide) p (plane_0_1_6_sound p h0) (plane_0_1_9_sound p h0) (plane_1_5_6_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_6_6 plane_1_6_8 590105431712 569141090689 520176509
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_6_6_sound p h1) (plane_1_6_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_1_8 plane_0_1_9 plane_1_7_7 6294126022 53876670249 71509664711
      (by decide) p (plane_0_1_8_sound p h0) (plane_0_1_9_sound p h0) (plane_1_7_7_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_8_4 plane_1_8_15 1676082744797 843242931158 67699997
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_8_4_sound p h1) (plane_1_8_15_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_1_7 plane_0_1_9 plane_1_9_9 9078349777 532335567341 527155870326
      (by decide) p (plane_0_1_7_sound p h0) (plane_0_1_9_sound p h0) (plane_1_9_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_1_7 plane_0_1_9 plane_1_10_10 9078349777 532335567341 527155870326
      (by decide) p (plane_0_1_7_sound p h0) (plane_0_1_9_sound p h0) (plane_1_10_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_1_8 plane_0_1_9 plane_1_11_11 2145067255 138389323997 143019329422
      (by decide) p (plane_0_1_8_sound p h0) (plane_0_1_9_sound p h0) (plane_1_11_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_12_12 plane_1_12_18 226264453585 263108869177 12588252044
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_12_12_sound p h1) (plane_1_12_18_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_1_7 plane_0_1_9 plane_1_13_13 520176509 546434044369 527155870326
      (by decide) p (plane_0_1_7_sound p h0) (plane_0_1_9_sound p h0) (plane_1_13_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_14_6 plane_1_14_16 73096149866 23918988107 635313193
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_14_6_sound p h1) (plane_1_14_16_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_1_9 plane_1_15_13 plane_1_15_15 569452994580 4222434513 564918656176
      (by decide) p (plane_0_1_9_sound p h0) (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_1
