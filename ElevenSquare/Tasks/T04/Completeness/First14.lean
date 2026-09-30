import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 14.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_14_12_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 14)
    (e1 : labels 1 = 12)
    (e2 : labels 2 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 14 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 12 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 8 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_4 plane_3_0_6 1124082257821 10571859773 568581733094
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_4 plane_3_1_9 67699997 286058466951 568581733094
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_4_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_4 plane_3_2_10 8058987727 296610908583 568581733094
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_4_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_8 plane_3_3_11 32358495242 249154618709 282458329541
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_8_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_4 plane_3_4_10 1131762613157 21090479789 568581733094
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_4_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_8 plane_3_5_11 549569533268 28422632345 282458329541
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_8_sound p h2) (plane_3_5_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_12_17 plane_3_6_11 plane_3_6_14 91691309771 14975876152 82910326544
      (by decide) p (plane_1_12_17_sound p h1) (plane_3_6_11_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_8 plane_3_7_15 12743111940 282557077259 282458329541
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_8_sound p h2) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_3_8_13 plane_3_8_16 246106080017 249154618709 84016202474
      (by decide) p (plane_0_14_14_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_4 plane_3_9_15 1131762613157 21090479789 568581733094
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_4_sound p h2) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_12_17 plane_3_10_19 7622387976 6715308053 8565695168
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_12_17_sound p h1) (plane_3_10_19_sound p h3))
  · refine ⟨(200 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row200]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_16 plane_3_12_14 25821040542 12984234492 14631772763
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_16_sound p h2) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_16 plane_3_13_14 226688241726 184172073764 248740136971
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_16_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_8_16 plane_3_14_14 plane_3_14_15 71509664711 53876670249 6294126022
      (by decide) p (plane_2_8_16_sound p h2) (plane_3_14_14_sound p h3) (plane_3_14_15_sound p h3))
  · refine ⟨(201 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row201]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_14_13_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 14)
    (e1 : labels 1 = 13)
    (e2 : labels 2 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 14 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 4 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_4_4 plane_3_0_6 565506734706 10571859773 286123403553
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_4_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_4 plane_3_1_7 plane_3_1_9 1052207326 8428013 1050521497
      (by decide) p (plane_2_4_4_sound p h2) (plane_3_1_7_sound p h3) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_13_19 plane_3_2_10 3310824502 98870302861 188479610895
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_13_19_sound p h1) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_13_19 plane_3_3_11 58966354913 249154618709 565438832685
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_13_19_sound p h1) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_3_4_5 plane_3_4_10 772314432417 21090479789 377406821981
      (by decide) p (plane_0_14_14_sound p h0) (plane_3_4_5_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_13_18 plane_3_5_11 549810954471 28422632345 277812578482
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_13_18_sound p h1) (plane_3_5_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_0_14_17 plane_3_6_15 204073209213 198540874785 279339316598
      (by decide) p (plane_0_14_14_sound p h0) (plane_0_14_17_sound p h0) (plane_3_6_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_17 plane_1_13_18 plane_3_7_15 104793484997 92227723283 194279197068
      (by decide) p (plane_0_14_17_sound p h0) (plane_1_13_18_sound p h1) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_4_12 plane_3_8_13 268090853421 84016202474 282458329541
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_4_12_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_3_9_10 plane_3_9_17 301116641534 296610908583 177450394996
      (by decide) p (plane_0_14_14_sound p h0) (plane_3_9_10_sound p h3) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_4_12 plane_3_10_10 234817143 289889229815 282458329541
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_4_12_sound p h2) (plane_3_10_10_sound p h3))
  · refine ⟨(202 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row202]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_4_12 plane_3_12_14 517211038026 220731986364 282458329541
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_4_12_sound p h2) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_4_12 plane_3_13_14 273061638778 184172073764 282458329541
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_4_12_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_12 plane_3_14_14 plane_3_14_15 143019329422 138389323997 2145067255
      (by decide) p (plane_2_4_12_sound p h2) (plane_3_14_14_sound p h3) (plane_3_14_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_18 plane_2_4_12 plane_3_15_15 4445101833 97786266987 92227723283
      (by decide) p (plane_1_13_18_sound p h1) (plane_2_4_12_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_14_13_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 14)
    (e1 : labels 1 = 13)
    (e2 : labels 2 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 14 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 8 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_4 plane_3_0_6 1124082257821 10571859773 568581733094
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_4 plane_3_1_9 67699997 286058466951 568581733094
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_4_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_4 plane_3_2_10 8058987727 296610908583 568581733094
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_4_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_8 plane_3_3_11 32358495242 249154618709 282458329541
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_8_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_4 plane_3_4_10 1131762613157 21090479789 568581733094
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_4_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_8 plane_3_5_11 549569533268 28422632345 282458329541
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_8_sound p h2) (plane_3_5_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_8 plane_3_6_15 280833965361 198540874785 282458329541
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_8_sound p h2) (plane_3_6_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_8 plane_3_7_15 12743111940 282557077259 282458329541
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_8_sound p h2) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_3_8_13 plane_3_8_16 246106080017 249154618709 84016202474
      (by decide) p (plane_0_14_14_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_3_9_10 plane_3_9_17 301116641534 296610908583 177450394996
      (by decide) p (plane_0_14_14_sound p h0) (plane_3_9_10_sound p h3) (plane_3_9_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_16 plane_3_10_15 240683185084 91348355030 248740136971
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_16_sound p h2) (plane_3_10_15_sound p h3))
  · refine ⟨(203 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row203]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_16 plane_3_12_14 25821040542 12984234492 14631772763
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_16_sound p h2) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_8_16 plane_3_13_14 226688241726 184172073764 248740136971
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_8_16_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_8_16 plane_3_14_14 plane_3_14_15 71509664711 53876670249 6294126022
      (by decide) p (plane_2_8_16_sound p h2) (plane_3_14_14_sound p h3) (plane_3_14_15_sound p h3))
  · refine ⟨(204 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row204]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_14_14_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 14)
    (e1 : labels 1 = 14)
    (e2 : labels 2 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 14 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_14_17 plane_3_2_7 plane_3_2_10 257471966024 101720067329 255017322744
      (by decide) p (plane_0_14_17_sound p h0) (plane_3_2_7_sound p h3) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_17 plane_2_4_4 plane_3_3_11 8438500783 20145485859 32595422329
      (by decide) p (plane_0_14_17_sound p h0) (plane_2_4_4_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_3_4_5 plane_3_4_10 772314432417 12377849851 381829087459
      (by decide) p (plane_1_14_14_sound p h1) (plane_3_4_5_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_4_4 plane_3_5_11 555849206859 19913735575 286092288567
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_4_4_sound p h2) (plane_3_5_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_17 plane_1_14_17 plane_3_6_11 59062152895 74075233124 48569799267
      (by decide) p (plane_0_14_17_sound p h0) (plane_1_14_17_sound p h1) (plane_3_6_11_sound p h3))
  · refine ⟨(205 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row205]
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
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_4_12 plane_3_10_10 234817143 289994215265 282557077259
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_4_12_sound p h2) (plane_3_10_10_sound p h3))
  · refine ⟨(206 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row206]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_4_12 plane_3_12_14 517211038026 228826401396 282557077259
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_4_12_sound p h2) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_4_12 plane_3_13_14 273061638778 188469167116 282557077259
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_4_12_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_12 plane_3_14_14 plane_3_14_15 143019329422 138389323997 2145067255
      (by decide) p (plane_2_4_12_sound p h2) (plane_3_14_14_sound p h3) (plane_3_14_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_3 plane_2_4_12 plane_3_15_15 17780407332000000 534921 528190
      (by decide) p (plane_0_14_3_sound p h0) (plane_2_4_12_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_14_14_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 14)
    (e1 : labels 1 = 14)
    (e2 : labels 2 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 14 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 14 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 8 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_8_4 plane_3_0_6 1124082257821 1917121227 568649365826
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_8_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_8_4 plane_3_1_9 67699997 286091972249 568649365826
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_8_4_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_8_4 plane_3_2_10 8058987727 296584132177 568649365826
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_8_4_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_8_8 plane_3_3_11 32358495242 248740136971 282557077259
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_8_8_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_8_4 plane_3_4_10 1131762613157 12377849851 568649365826
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_8_4_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_8_8 plane_3_5_11 549569533268 19913735575 282557077259
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_8_8_sound p h2) (plane_3_5_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_17 plane_2_8_8 plane_3_6_11 268090853421 236248611580 92227723283
      (by decide) p (plane_1_14_17_sound p h1) (plane_2_8_8_sound p h2) (plane_3_6_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_8_8 plane_3_7_15 12743111940 282458329541 282557077259
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_8_8_sound p h2) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_1_14_16 plane_3_8_13 242489795606 44100614743 263577935163
      (by decide) p (plane_1_14_14_sound p h1) (plane_1_14_16_sound p h1) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_8_4 plane_3_9_15 1131762613157 12377849851 568649365826
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_8_4_sound p h2) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_1_14_16 plane_3_10_15 253947212243 47868557605 263577935163
      (by decide) p (plane_1_14_14_sound p h1) (plane_1_14_16_sound p h1) (plane_3_10_15_sound p h3))
  · refine ⟨(207 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row207]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_1_14_17 plane_3_12_14 218315607360 114413200698 139669658299
      (by decide) p (plane_1_14_14_sound p h1) (plane_1_14_17_sound p h1) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_1_14_16 plane_3_13_14 238494224500 94234583558 263577935163
      (by decide) p (plane_1_14_14_sound p h1) (plane_1_14_16_sound p h1) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_14_17 plane_3_14_14 plane_3_14_15 286038658844 148996200585 97622805133
      (by decide) p (plane_1_14_17_sound p h1) (plane_3_14_14_sound p h3) (plane_3_14_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_14_3 plane_1_14_17 plane_3_15_15 130381689316000000 178307 173613
      (by decide) p (plane_0_14_3_sound p h0) (plane_1_14_17_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_14_12 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 14)
    (e1 : labels 1 = 12)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 14 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 12 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_12_18 plane_2_0_8 65045933361 286123403553 526217738354
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_12_18_sound p h1) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_12_18 plane_2_1_9 65326480587 286091972249 526217738354
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_12_18_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_12_18 plane_2_2_10 60329575017 296584132177 526217738354
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_12_18_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_12_18 plane_2_3_6 21137808724 1834419740 23918988107
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_12_18_sound p h1) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_12_18 plane_2_4_12 48652965083 282458329541 526217738354
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_12_18_sound p h1) (plane_2_4_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_12_18 plane_2_5_13 74753504753 289994215265 526217738354
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_12_18_sound p h1) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_6_8 plane_2_6_14 577364467412 289994215265 12377849851
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_6_8_sound p h2) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_7_6 plane_2_7_19 543733002463 568581733094 208382902691
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_7_6_sound p h2) (plane_2_7_19_sound p h2))
  · exact complete_14_12_8 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_12_17 plane_2_9_12 plane_2_9_17 284027168089 41390492312 225578898288
      (by decide) p (plane_1_12_17_sound p h1) (plane_2_9_12_sound p h2) (plane_2_9_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_10_13 plane_2_10_18 283358547227 286091972249 108114965061
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_10_13_sound p h2) (plane_2_10_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_11_13 plane_2_11_19 569452994580 286123403553 12377849851
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_3 plane_0_14_19 plane_2_12_12 108426769676000000 232722 268211
      (by decide) p (plane_0_14_3_sound p h0) (plane_0_14_19_sound p h0) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_0_14_19 plane_2_13_12 207193100746 208382902691 286195087637
      (by decide) p (plane_0_14_14_sound p h0) (plane_0_14_19_sound p h0) (plane_2_13_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_0_14_15 plane_2_14_17 148996200585 97622805133 286038658844
      (by decide) p (plane_0_14_14_sound p h0) (plane_0_14_15_sound p h0) (plane_2_14_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_0_14_19 plane_2_15_17 565096908217 1917121227 286195087637
      (by decide) p (plane_0_14_14_sound p h0) (plane_0_14_19_sound p h0) (plane_2_15_17_sound p h2))

theorem complete_14_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 14)
    (e1 : labels 1 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 14 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_13_19 plane_2_0_8 3421283912 95374467851 188479610895
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_13_19_sound p h1) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_13_19 plane_2_1_9 10571859773 286091972249 565438832685
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_13_19_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_2_4 plane_2_2_10 586247925188 296584132177 1917121227
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_13_19 plane_2_3_6 98256342376 8071446856 113087766537
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_13_19_sound p h1) (plane_2_3_6_sound p h2))
  · exact complete_14_13_4 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_13_18 plane_2_5_13 107782611209 289994215265 277812578482
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_13_18_sound p h1) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_6_8 plane_2_6_14 577364467412 289994215265 12377849851
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_6_8_sound p h2) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_7_6 plane_2_7_19 543733002463 568581733094 208382902691
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_7_6_sound p h2) (plane_2_7_19_sound p h2))
  · exact complete_14_13_8 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_9_8 plane_2_9_12 271974970539 88201229486 194257100055
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_9_8_sound p h2) (plane_2_9_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_10_13 plane_2_10_18 283358547227 286091972249 108114965061
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_10_13_sound p h2) (plane_2_10_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_2_11_13 plane_2_11_19 569452994580 286123403553 12377849851
      (by decide) p (plane_0_14_14_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_19 plane_1_13_16 plane_2_12_12 28477460708 27106692419 59835745884
      (by decide) p (plane_0_14_19_sound p h0) (plane_1_13_16_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_0_14_19 plane_2_13_12 207193100746 208382902691 286195087637
      (by decide) p (plane_0_14_14_sound p h0) (plane_0_14_19_sound p h0) (plane_2_13_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_13_12 plane_2_14_17 194580865167 97622805133 273581663960
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_13_12_sound p h1) (plane_2_14_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_13_16 plane_2_15_17 491281711880 1917121227 248405159872
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_13_16_sound p h1) (plane_2_15_17_sound p h2))

theorem complete_14_14 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 14)
    (e1 : labels 1 = 14)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 14 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 14 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_14_3 plane_0_14_16 plane_2_0_8 230240398092000000 534921 984719
      (by decide) p (plane_0_14_3_sound p h0) (plane_0_14_16_sound p h0) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_16 plane_2_1_4 plane_2_1_9 286195087637 57265570853 508188953156
      (by decide) p (plane_0_14_16_sound p h0) (plane_2_1_4_sound p h2) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_16 plane_2_2_4 plane_2_2_10 586247925188 66771606715 1042442973009
      (by decide) p (plane_0_14_16_sound p h0) (plane_2_2_4_sound p h2) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_16 plane_1_14_14 plane_2_3_6 18279956300 224275553756 263108869177
      (by decide) p (plane_0_14_16_sound p h0) (plane_1_14_14_sound p h1) (plane_2_3_6_sound p h2))
  · exact complete_14_14_4 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_14_17 plane_2_5_8 plane_2_5_13 288387185670 94423090859 246619005718
      (by decide) p (plane_0_14_17_sound p h0) (plane_2_5_8_sound p h2) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_6_8 plane_2_6_14 577364467412 289889229815 21090479789
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_6_8_sound p h2) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_7_6 plane_2_7_19 543733002463 568649365826 212594706109
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_7_6_sound p h2) (plane_2_7_19_sound p h2))
  · exact complete_14_14_8 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_1_14_17 plane_2_9_8 204073209213 198540874785 279339316598
      (by decide) p (plane_1_14_14_sound p h1) (plane_1_14_17_sound p h1) (plane_2_9_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_10_12 plane_2_10_18 556142498998 286058466951 28422632345
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_10_12_sound p h2) (plane_2_10_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_2_11_13 plane_2_11_19 569452994580 286092288567 21090479789
      (by decide) p (plane_1_14_14_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_3 plane_1_14_16 plane_2_12_12 13926144644000000 465444 984719
      (by decide) p (plane_0_14_3_sound p h0) (plane_1_14_16_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_17 plane_2_13_12 plane_2_13_13 284027168089 101720067329 194580865167
      (by decide) p (plane_1_14_17_sound p h1) (plane_2_13_12_sound p h2) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_14_17 plane_2_14_17 236488775885 97622805133 277812578482
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_14_17_sound p h1) (plane_2_14_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_14_14 plane_1_14_16 plane_2_15_17 1039767016309 10571859773 527155870326
      (by decide) p (plane_1_14_14_sound p h1) (plane_1_14_16_sound p h1) (plane_2_15_17_sound p h2))

theorem complete_14 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 14)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 14 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_0_6 plane_1_0_8 188531829352 1407478171 188479610895
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_1_9 plane_1_1_15 70594549606 69460547119 547295495
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_1_9_sound p h1) (plane_1_1_15_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_0_14_16 plane_1_2_10 546434044369 520176509 527155870326
      (by decide) p (plane_0_14_14_sound p h0) (plane_0_14_16_sound p h0) (plane_1_2_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_3_5 plane_1_3_11 226264453585 12588252044 263108869177
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_3_5_sound p h1) (plane_1_3_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_0_14_19 plane_1_4_12 281223749827 4290134510 286195087637
      (by decide) p (plane_0_14_14_sound p h0) (plane_0_14_19_sound p h0) (plane_1_4_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_5_13 plane_1_5_15 577364467412 560062740912 9078349777
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_5_13_sound p h1) (plane_1_5_15_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_6_14 plane_1_6_15 288387185670 278391974979 9078349777
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_6_14_sound p h1) (plane_1_6_15_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_7_8 plane_1_7_19 1676082744797 67699997 843242931158
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_7_8_sound p h1) (plane_1_7_19_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_0_14_15 plane_1_8_16 53876670249 6294126022 71509664711
      (by decide) p (plane_0_14_14_sound p h0) (plane_0_14_15_sound p h0) (plane_1_8_16_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_1_9_17 plane_1_9_19 586247925188 564918656176 520176509
      (by decide) p (plane_0_14_14_sound p h0) (plane_1_9_17_sound p h1) (plane_1_9_19_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_0_14_17 plane_1_10_17 41766690707 141095471221 139669658299
      (by decide) p (plane_0_14_14_sound p h0) (plane_0_14_17_sound p h0) (plane_1_10_17_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_14_14 plane_0_14_16 plane_1_11_19 1050521497 8428013 1052207326
      (by decide) p (plane_0_14_14_sound p h0) (plane_0_14_16_sound p h0) (plane_1_11_19_sound p h1))
  · exact complete_14_12 labels p h e0 he
  · exact complete_14_13 labels p h e0 he
  · exact complete_14_14 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_14_3 plane_0_14_17 plane_1_15_18 35948473292000000 536422 520839
      (by decide) p (plane_0_14_3_sound p h0) (plane_0_14_17_sound p h0) (plane_1_15_18_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_14
