import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 10.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_10_8_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 8)
    (e2 : labels 2 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 8 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_8_4 plane_3_0_8 378632391 568648995369 1130136737677
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_8_4_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_8_4 plane_3_1_9 67699997 568581733094 1130136737677
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_8_4_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_8_4 plane_3_2_10 8058987727 589557157165 1130136737677
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_8_4_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_8_8 plane_3_3_11 32358495242 252961440741 286171280935
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_8_8_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_8_4 plane_3_4_10 1131762613157 30610409268 576194818729
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_8_4_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_8_8 plane_3_5_13 234817143 289889229815 282458329541
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_8_8_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_1_8_13 plane_3_6_14 93829213027 289889229815 274101840469
      (by decide) p (plane_0_10_18_sound p h0) (plane_1_8_13_sound p h1) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_17 plane_2_8_8 plane_3_7_14 89441890188 2350535303 67219107427
      (by decide) p (plane_1_8_17_sound p h1) (plane_2_8_8_sound p h2) (plane_3_7_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_3_8_13 plane_3_8_16 246106080017 252961440741 80715855727
      (by decide) p (plane_0_10_10_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_13 plane_3_9_15 plane_3_9_17 590105431712 87603658687 539094743595
      (by decide) p (plane_1_8_13_sound p h1) (plane_3_9_15_sound p h3) (plane_3_9_17_sound p h3))
  · refine ⟨(145 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row145]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_8_17 plane_3_11_14 plane_3_11_19 13624877678 9931292687 9858040810
      (by decide) p (plane_1_8_17_sound p h1) (plane_3_11_14_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_8_16 plane_3_12_17 70756482496 11009702152 83887568097
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_8_16_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_8_17 plane_3_13_14 9116359226 60702206202 68911691945
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_8_17_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_8_16 plane_3_14_14 25176504088 286058466951 248740136971
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_8_16_sound p h2) (plane_3_14_14_sound p h3))
  · refine ⟨(146 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row146]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_10_8_12 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 8)
    (e2 : labels 2 = 12)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 12 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_12_12 plane_3_0_8 8438500783 189549665123 164800102146
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_12_12_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_12_12 plane_3_1_9 12588252044 284290866547 247200153219
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_12_12_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_12_12 plane_3_2_10 29600136713 589557157165 494400306438
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_12_12_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_1_8_14 plane_3_3_14 219653794147 311530025499 277886303201
      (by decide) p (plane_0_10_18_sound p h0) (plane_1_8_14_sound p h1) (plane_3_3_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_12_12 plane_3_4_12 16179247621 280812131798 247200153219
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_12_12_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_12_12 plane_3_5_13 21478273037 576194818729 494400306438
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_12_12_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_12_12 plane_3_6_14 21478273037 576194818729 494400306438
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_12_12_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_12_12 plane_3_7_17 plane_3_7_19 1123889340121 57673997591 435012931568
      (by decide) p (plane_2_12_12_sound p h2) (plane_3_7_17_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_3_8_13 plane_3_8_16 246106080017 252961440741 80715855727
      (by decide) p (plane_0_10_10_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_12_17 plane_3_9_15 plane_3_9_17 73763178964 32125196257 7752048309
      (by decide) p (plane_2_12_17_sound p h2) (plane_3_9_15_sound p h3) (plane_3_9_17_sound p h3))
  · refine ⟨(147 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row147]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_12_12 plane_3_11_13 plane_3_11_19 189817664860 8438500783 165657187841
      (by decide) p (plane_2_12_12_sound p h2) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_11 plane_3_12_14 74242634416 71711908354 91691309771
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_11_sound p h0) (plane_3_12_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_11 plane_2_12_17 plane_3_13_19 70605495944 562284082837 293658608088
      (by decide) p (plane_0_10_11_sound p h0) (plane_2_12_17_sound p h2) (plane_3_13_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_19 plane_2_12_17 plane_3_14_14 8565695168 6715308053 7622387976
      (by decide) p (plane_0_10_19_sound p h0) (plane_2_12_17_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_19 plane_2_12_12 plane_3_15_14 265998687433 153753283400 194526752133
      (by decide) p (plane_0_10_19_sound p h0) (plane_2_12_12_sound p h2) (plane_3_15_14_sound p h3))

theorem complete_10_8_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 8)
    (e2 : labels 2 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 13 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_13_13 plane_3_0_8 358053342 286092288567 296584132177
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_13_13_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_13_13 plane_3_1_9 520176509 286058466951 296584132177
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_13_13_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_13_13 plane_3_2_10 3627754886 589557157165 589503107161
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_13_13_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_13_13 plane_3_3_14 258712527776 623060050998 296584132177
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_13_13_sound p h2) (plane_3_3_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_2_13_13 plane_3_4_12 8417041069 561624263596 589503107161
      (by decide) p (plane_1_8_4_sound p h1) (plane_2_13_13_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_13_13 plane_3_5_13 5338712606 289889229815 296584132177
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_13_13_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_13_13 plane_3_6_14 5338712606 289889229815 296584132177
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_13_13_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_13 plane_3_7_15 plane_3_7_17 566754254278 578265315311 8417041069
      (by decide) p (plane_2_13_13_sound p h2) (plane_3_7_15_sound p h3) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_3_8_13 plane_3_8_16 246106080017 252961440741 80715855727
      (by decide) p (plane_0_10_10_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_13_13 plane_3_9_14 146790202854 59270785703 150282144431
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_13_13_sound p h2) (plane_3_9_14_sound p h3))
  · refine ⟨(148 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row148]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_8_17 plane_3_11_14 plane_3_11_19 13624877678 9931292687 9858040810
      (by decide) p (plane_1_8_17_sound p h1) (plane_3_11_14_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_11 plane_3_12_17 64183263944 11009702152 91691309771
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_11_sound p h0) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_15 plane_3_13_14 12250414744 10117034367 16021510315
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_15_sound p h0) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_15 plane_1_8_16 plane_3_14_14 248740136971 91348355030 240683185084
      (by decide) p (plane_0_10_15_sound p h0) (plane_1_8_16_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_19 plane_2_13_16 plane_3_15_14 16091708513 19219160425 27631156413
      (by decide) p (plane_0_10_19_sound p h0) (plane_2_13_16_sound p h2) (plane_3_15_14_sound p h3))

theorem complete_10_9_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 9)
    (e2 : labels 2 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_9_9 plane_3_3_11 1130435423 13313760039 15474998134
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_9_9_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_9_9 plane_3_4_10 248732509 13205526 126844247
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_9_9_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_13 plane_3_5_10 plane_3_5_13 144488640871 59270785703 118244314584
      (by decide) p (plane_0_10_13_sound p h0) (plane_3_5_10_sound p h3) (plane_3_5_13_sound p h3))
  · refine ⟨(149 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row149]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_9_9 plane_3_7_10 279203399763 87603658687 300648190012
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_9_9_sound p h2) (plane_3_7_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_9_17 plane_3_8_13 282973951883 80715855727 300564288862
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_9_17_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_3_9_10 plane_3_9_14 7604665309 3119515037 4609327155
      (by decide) p (plane_0_10_10_sound p h0) (plane_3_9_10_sound p h3) (plane_3_9_14_sound p h3))
  · refine ⟨(150 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row150]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_9_14 plane_1_9_17 plane_3_11_14 47614852103 123563208361 146115791345
      (by decide) p (plane_1_9_14_sound p h1) (plane_1_9_17_sound p h1) (plane_3_11_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_9_17 plane_3_12_17 6763199212 869187012 7909586549
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_9_17_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_9_17 plane_3_13_14 144976325411 91053309303 150282144431
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_9_17_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_9_17 plane_3_14_14 27377711 15257327885 15819173098
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_9_17_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_9_17 plane_3_15_14 37046456527 25173651202 38437018581
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_9_17_sound p h2) (plane_3_15_14_sound p h3))

theorem complete_10_9_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 9)
    (e2 : labels 2 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_13_13 plane_3_2_10 1813877443 150324095006 150282144431
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_13_13_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_13_13 plane_3_3_11 29600136713 252961440741 300564288862
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_13_13_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_13_13 plane_3_4_12 8417041069 286480696885 300564288862
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_13_13_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_13_13 plane_3_5_13 157020959 8840126143 9044004372
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_13_13_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_13_13 plane_3_6_14 157020959 8840126143 9044004372
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_13_13_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_13 plane_3_7_15 plane_3_7_17 566754254278 578265315311 8417041069
      (by decide) p (plane_2_13_13_sound p h2) (plane_3_7_15_sound p h3) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_3_8_13 plane_3_8_16 246106080017 252961440741 80715855727
      (by decide) p (plane_0_10_10_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_13_13 plane_3_9_14 146790202854 59270785703 150282144431
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_13_13_sound p h2) (plane_3_9_14_sound p h3))
  · refine ⟨(151 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row151]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_13_13 plane_3_11_14 11412680983 3662680931 11826774948
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_13_13_sound p h2) (plane_3_11_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_11 plane_3_12_17 64183263944 11009702152 91691309771
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_11_sound p h0) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_15 plane_3_13_14 12250414744 10117034367 16021510315
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_15_sound p h0) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_15 plane_1_9_17 plane_3_14_14 296584132177 91348355030 296729705558
      (by decide) p (plane_0_10_15_sound p h0) (plane_1_9_17_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_12 plane_1_9_17 plane_3_15_14 28769887088 30598113403 40575309727
      (by decide) p (plane_1_9_12_sound p h1) (plane_1_9_17_sound p h1) (plane_3_15_14_sound p h3))

theorem complete_10_10_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 4 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_2_4_4 plane_2_4_10 plane_3_0_6 22752306341 282753367353 284726497290
      (by decide) p (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_4_4 plane_3_1_9 1407478171 95352822317 95374467851
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_4_4_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_2_4_10 plane_3_2_10 295155055633 97445420627 273901749379
      (by decide) p (plane_0_10_17_sound p h0) (plane_2_4_10_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_2_4_10 plane_3_3_11 496971563523 188718161132 547803498758
      (by decide) p (plane_0_10_17_sound p h0) (plane_2_4_10_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_10 plane_3_4_4 plane_3_4_10 94908832430 11099928857 94869191801
      (by decide) p (plane_2_4_10_sound p h2) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_2_4_10 plane_3_5_10 117984500434 174546968281 273901749379
      (by decide) p (plane_0_10_17_sound p h0) (plane_2_4_10_sound p h2) (plane_3_5_10_sound p h3))
  · refine ⟨(152 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row152]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_3_7_10 plane_3_7_15 90658323513 63443117992 70761576674
      (by decide) p (plane_0_10_17_sound p h0) (plane_3_7_10_sound p h3) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_10 plane_2_4_12 plane_3_8_13 268090853421 155354934215 561792632189
      (by decide) p (plane_2_4_10_sound p h2) (plane_2_4_12_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_10 plane_2_4_12 plane_3_9_10 281713496990 340592954994 561792632189
      (by decide) p (plane_2_4_10_sound p h2) (plane_2_4_12_sound p h2) (plane_3_9_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_4_12 plane_2_4_13 plane_3_10_10 92989527540 78272381 90658323513
      (by decide) p (plane_2_4_12_sound p h2) (plane_2_4_13_sound p h2) (plane_3_10_10_sound p h3))
  · refine ⟨(153 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row153]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_4_10 plane_2_4_12 plane_3_12_17 244149399248 62016386472 561792632189
      (by decide) p (plane_2_4_10_sound p h2) (plane_2_4_12_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_4_12 plane_3_13_13 8417041069 296584132177 282557077259
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_4_12_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_4_12 plane_3_14_14 4290134510 286091972249 282557077259
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_4_12_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_18 plane_2_4_12 plane_3_15_15 4445101833 286123403553 282557077259
      (by decide) p (plane_1_10_18_sound p h1) (plane_2_4_12_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_10_10_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 10)
    (e2 : labels 2 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 9 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_9_9 plane_3_0_8 8920842114 286092288567 289994215265
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_9_9_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_9_9 plane_3_1_9 9078349777 286058466951 289994215265
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_9_9_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_9_9 plane_3_2_10 5338712606 296610908583 289994215265
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_9_9_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_9_9 plane_3_3_11 1130435423 13245405489 15457684384
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_9_9_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_3_4_4 plane_3_4_10 94908832430 551711303 48337256299
      (by decide) p (plane_1_10_10_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_9_9 plane_3_5_10 1866373621 690744503 1932210548
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_9_9_sound p h2) (plane_3_5_10_sound p h3))
  · refine ⟨(154 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row154]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_3_7_10 plane_3_7_15 90658323513 63443117992 70761576674
      (by decide) p (plane_0_10_17_sound p h0) (plane_3_7_10_sound p h3) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_9_17 plane_3_8_13 282973951883 93829213027 300648190012
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_9_17_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_1_10_13 plane_3_9_10 108257512397 94515900045 144488640871
      (by decide) p (plane_1_10_10_sound p h1) (plane_1_10_13_sound p h1) (plane_3_9_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_13 plane_3_10_10 plane_3_10_15 144193592835 123563208361 52496582228
      (by decide) p (plane_1_10_13_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_15_sound p h3))
  · refine ⟨(155 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row155]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_9_17 plane_3_12_17 3381599606 591153006 3955897237
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_9_17_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_9_17 plane_3_13_14 144976325411 91053309303 150282144431
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_9_17_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_9_17 plane_3_14_14 27377711 15257327885 15819173098
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_9_17_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_10_13 plane_1_10_18 plane_3_15_15 286123403553 108281777256 283358547227
      (by decide) p (plane_1_10_13_sound p h1) (plane_1_10_18_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_10_12_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 12)
    (e2 : labels 2 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 12 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 8 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_8_4 plane_3_0_8 378632391 289926042144 576194818729
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_8_4_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_8_4 plane_3_1_9 67699997 289889229815 576194818729
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_8_4_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_8_4 plane_3_2_10 8058987727 300648190012 576194818729
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_8_4_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_8_8 plane_3_3_11 32358495242 252961440741 286171280935
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_8_8_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_8_4 plane_3_4_10 1131762613157 30610409268 576194818729
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_8_4_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_12_12 plane_2_8_8 plane_3_5_10 281478679847 122709280975 245232080481
      (by decide) p (plane_1_12_12_sound p h1) (plane_2_8_8_sound p h2) (plane_3_5_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_1_12_17 plane_3_6_14 44927628456 289889229815 248405159872
      (by decide) p (plane_0_10_18_sound p h0) (plane_1_12_17_sound p h1) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_1_12_17 plane_3_7_19 36304678392 284324682913 124202579936
      (by decide) p (plane_0_10_18_sound p h0) (plane_1_12_17_sound p h1) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_3_8_13 plane_3_8_16 246106080017 252961440741 80715855727
      (by decide) p (plane_0_10_10_sound p h0) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_12_12 plane_2_8_8 plane_3_9_15 562547462351 68452719217 245232080481
      (by decide) p (plane_1_12_12_sound p h1) (plane_2_8_8_sound p h2) (plane_3_9_15_sound p h3))
  · refine ⟨(156 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row156]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_1_12_17 plane_3_11_19 40226167464 286092288567 248405159872
      (by decide) p (plane_0_10_18_sound p h0) (plane_1_12_17_sound p h1) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_8_16 plane_3_12_17 70756482496 11009702152 83887568097
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_8_16_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_12_12 plane_2_8_16 plane_3_13_14 226688241726 135560397220 214074416447
      (by decide) p (plane_1_12_12_sound p h1) (plane_2_8_16_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_8_16 plane_3_14_14 25176504088 286058466951 248740136971
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_8_16_sound p h2) (plane_3_14_14_sound p h3))
  · refine ⟨(157 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row157]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_10_13_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 13)
    (e2 : labels 2 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 4 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_4_4 plane_3_0_6 94251122451 1655412251 49440629994
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_4_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_3_1_9 296584132177 184172073764 289952650822
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_3_2_10 153758773765 97445420627 144976325411
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_3_3_11 258269678195 188718161132 289952650822
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_3_4_4 plane_3_4_10 284726497290 10415553607 148309456911
      (by decide) p (plane_1_13_13_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_3_5_10 58030405710 174546968281 144976325411
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_3_5_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_14 plane_2_4_13 plane_3_6_15 21350669565 8154722029 22367449111
      (by decide) p (plane_1_13_14_sound p h1) (plane_2_4_13_sound p h2) (plane_3_6_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_3_7_10 plane_3_7_15 90658323513 63443117992 70761576674
      (by decide) p (plane_0_10_17_sound p h0) (plane_3_7_10_sound p h3) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_4_12 plane_3_8_6 541387309342 579624683659 292859327197
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_4_12_sound p h2) (plane_3_8_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_3_9_15 10415553607 284800700977 144976325411
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_3_9_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_4_12 plane_3_10_10 234817143 300564288862 292859327197
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_4_12_sound p h2) (plane_3_10_10_sound p h3))
  · refine ⟨(158 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row158]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_4_12 plane_3_12_17 4002449168 628783432 4800972577
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_4_12_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_4_12 plane_3_13_14 273061638778 191456736110 292859327197
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_4_12_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_4_12 plane_3_14_14 4290134510 286058466951 282458329541
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_4_12_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_4_12 plane_3_15_15 4445101833 286092288567 282458329541
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_4_12_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_10_13_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 13)
    (e2 : labels 2 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 8 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_8_4 plane_3_0_6 1124082257821 9932473506 589503107161
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_8_4_sound p h2) (plane_3_0_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_8_4 plane_3_1_9 67699997 296584132177 589503107161
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_8_4_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_8_4 plane_3_2_10 8058987727 307517547530 589503107161
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_8_4_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_8_8 plane_3_3_11 32358495242 258269678195 292859327197
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_8_8_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_8_4 plane_3_4_10 1131762613157 20831107214 589503107161
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_8_4_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_8_8 plane_3_5_13 234817143 289889229815 282458329541
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_8_8_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_8_8 plane_2_8_13 plane_3_6_15 11497565201 31203773929 30219441171
      (by decide) p (plane_2_8_8_sound p h2) (plane_2_8_13_sound p h2) (plane_3_6_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_8_8 plane_3_7_15 12743111940 292938243343 292859327197
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_8_8_sound p h2) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_3_8_13 plane_3_8_16 246106080017 258269678195 87603658687
      (by decide) p (plane_1_13_13_sound p h1) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_8_8 plane_3_9_15 562547462351 20831107214 292859327197
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_8_8_sound p h2) (plane_3_9_15_sound p h3))
  · refine ⟨(159 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row159]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(160 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row160]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_8_16 plane_3_12_17 3479827008 628783432 4228498969
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_8_16_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_8_16 plane_3_13_14 226688241726 191456736110 257938437109
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_8_16_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_8_16 plane_3_14_14 25176504088 286058466951 248740136971
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_8_16_sound p h2) (plane_3_14_14_sound p h3))
  · refine ⟨(161 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row161]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm

theorem complete_10_13_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 13)
    (e2 : labels 2 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 9 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_3_0_8 148309456911 92173301751 144976325411
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_3_1_9 296584132177 184172073764 289952650822
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_3_2_10 153758773765 97445420627 144976325411
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_3_3_11 258269678195 188718161132 289952650822
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_3_4_4 plane_3_4_10 284726497290 10415553607 148309456911
      (by decide) p (plane_1_13_13_sound p h1) (plane_3_4_4_sound p h3) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_3_5_10 58030405710 174546968281 144976325411
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_3_5_10_sound p h3))
  · refine ⟨(162 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row162]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_3_7_10 plane_3_7_15 90658323513 63443117992 70761576674
      (by decide) p (plane_0_10_17_sound p h0) (plane_3_7_10_sound p h3) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_9_17 plane_3_8_13 282973951883 87603658687 307496148648
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_9_17_sound p h2) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_3_9_15 10415553607 284800700977 144976325411
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_3_9_15_sound p h3))
  · refine ⟨(163 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row163]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(164 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row164]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_9_17 plane_3_12_17 32125196257 4794473669 38437018581
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_9_17_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_9_17 plane_3_13_14 144976325411 95728368055 153748074324
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_9_17_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_9_17 plane_3_14_14 520176509 296584132177 307496148648
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_9_17_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_9_17 plane_3_15_15 59675557 49436485637 51249358108
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_9_17_sound p h2) (plane_3_15_15_sound p h3))

theorem complete_10_13_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 13)
    (e2 : labels 2 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 13 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_13_13 plane_3_0_8 358053342 286092288567 296584132177
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_13_13_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_13_13 plane_3_1_9 520176509 286058466951 296584132177
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_13_13_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_13_13 plane_3_2_10 1813877443 153758773765 153748074324
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_13_13_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_13_13 plane_3_3_11 29600136713 258269678195 307496148648
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_13_13_sound p h2) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_13_13 plane_3_4_10 295155055633 10415553607 153748074324
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_13_13_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_13_13 plane_3_5_13 5338712606 289889229815 296584132177
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_13_13_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_2_13_13 plane_3_6_14 5338712606 289889229815 296584132177
      (by decide) p (plane_0_10_18_sound p h0) (plane_2_13_13_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_13_13 plane_3_7_15 8417041069 292938243343 307496148648
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_13_13_sound p h2) (plane_3_7_15_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_3_8_13 plane_3_8_16 246106080017 258269678195 87603658687
      (by decide) p (plane_1_13_13_sound p h1) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_13_13 plane_3_9_15 295155055633 10415553607 153748074324
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_13_13_sound p h2) (plane_3_9_15_sound p h3))
  · refine ⟨(165 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row165]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_13_12 plane_3_11_14 plane_3_11_19 286122431238 273727962933 121004392604
      (by decide) p (plane_2_13_12_sound p h2) (plane_3_11_14_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_11 plane_1_13_13 plane_3_12_17 38355789352 192549791832 288312664489
      (by decide) p (plane_0_10_11_sound p h0) (plane_1_13_13_sound p h1) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_3_13_14 plane_3_13_19 187214839747 4966236753 95728368055
      (by decide) p (plane_1_13_13_sound p h1) (plane_3_13_14_sound p h3) (plane_3_13_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_1_13_12 plane_3_14_14 208382902691 286058466951 273581663960
      (by decide) p (plane_0_10_18_sound p h0) (plane_1_13_12_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_13_12 plane_2_13_12 plane_3_15_14 394732355537 415576003437 109849895569
      (by decide) p (plane_1_13_12_sound p h1) (plane_2_13_12_sound p h2) (plane_3_15_14_sound p h3))

theorem complete_10_8 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 8)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 8 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_1_8_14 plane_2_0_8 28121870751 568711803093 1104672086663
      (by decide) p (plane_1_8_4_sound p h1) (plane_1_8_14_sound p h1) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_1_8_14 plane_2_1_9 28422632345 568649365826 1104672086663
      (by decide) p (plane_1_8_4_sound p h1) (plane_1_8_14_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_1_8_14 plane_2_2_10 21657103543 589503107161 1104672086663
      (by decide) p (plane_1_8_4_sound p h1) (plane_1_8_14_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_1_8_14 plane_2_3_11 31598666101 248740136971 555772606402
      (by decide) p (plane_0_10_18_sound p h0) (plane_1_8_14_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_8_14 plane_2_4_10 plane_2_4_12 561792632189 11327968305 1104901880803
      (by decide) p (plane_1_8_14_sound p h1) (plane_2_4_10_sound p h2) (plane_2_4_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_8_4 plane_1_8_14 plane_2_5_13 37825715679 576406739029 1104672086663
      (by decide) p (plane_1_8_4_sound p h1) (plane_1_8_14_sound p h1) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_1_8_14 plane_2_6_14 1990827141 15474998134 29625904745
      (by decide) p (plane_0_10_10_sound p h0) (plane_1_8_14_sound p h1) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_1_8_14 plane_2_7_15 2265593661 57234256187 112578438031
      (by decide) p (plane_0_10_10_sound p h0) (plane_1_8_14_sound p h1) (plane_2_7_15_sound p h2))
  · exact complete_10_8_8 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_8_13 plane_1_8_17 plane_2_9_17 216547944797 90948203851 284027168089
      (by decide) p (plane_1_8_13_sound p h1) (plane_1_8_17_sound p h1) (plane_2_9_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_15 plane_1_8_13 plane_2_10_13 303232933873 247126416722 175725312954
      (by decide) p (plane_0_10_15_sound p h0) (plane_1_8_13_sound p h1) (plane_2_10_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_11_13 plane_2_11_19 94908832430 48337256299 551711303
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact complete_10_8_12 labels p h e0 e1 he
  · exact complete_10_8_13 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_10_15 plane_2_14_14 plane_2_14_16 263577935163 253947212243 47868557605
      (by decide) p (plane_0_10_15_sound p h0) (plane_2_14_14_sound p h2) (plane_2_14_16_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_15_15 plane_2_15_17 282797744028 3615241625 145011768897
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2))

theorem complete_10_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 9 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_2_0_6 plane_2_0_8 282797744028 94168568283 275461549151
      (by decide) p (plane_0_10_17_sound p h0) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_1_9_15 plane_2_1_9 21090479789 289994215265 576561955862
      (by decide) p (plane_0_10_10_sound p h0) (plane_1_9_15_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_1_9_15 plane_2_2_10 6934120364 150282144431 288280977931
      (by decide) p (plane_0_10_10_sound p h0) (plane_1_9_15_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_1_9_15 plane_2_3_6 247986226244 22463814228 288280977931
      (by decide) p (plane_0_10_10_sound p h0) (plane_1_9_15_sound p h1) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_9_14 plane_1_9_17 plane_2_4_13 100955561673 100351480326 146115791345
      (by decide) p (plane_1_9_14_sound p h1) (plane_1_9_17_sound p h1) (plane_2_4_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_13 plane_1_9_17 plane_2_5_13 75162047503 26248291114 73395101427
      (by decide) p (plane_0_10_13_sound p h0) (plane_1_9_17_sound p h1) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_13 plane_2_6_13 108257512397 94515900045 144488640871
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_13_sound p h0) (plane_2_6_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_7_6 plane_2_7_15 53402669690 57234256187 41347015167
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_7_6_sound p h2) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_8_13 plane_2_8_17 284027168089 216547944797 90948203851
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_8_13_sound p h2) (plane_2_8_17_sound p h2))
  · exact complete_10_9_9 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_15 plane_2_10_13 123563208361 52496582228 144193592835
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_15_sound p h0) (plane_2_10_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_11_13 plane_2_11_19 94908832430 48337256299 551711303
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_9_12 plane_1_9_17 plane_2_12_17 41390492312 225578898288 284027168089
      (by decide) p (plane_1_9_12_sound p h1) (plane_1_9_17_sound p h1) (plane_2_12_17_sound p h2))
  · exact complete_10_9_13 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_10_15 plane_1_9_17 plane_2_14_14 26964628053 8703374110 26975427778
      (by decide) p (plane_0_10_15_sound p h0) (plane_1_9_17_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_15_15 plane_2_15_17 282797744028 3615241625 145011768897
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2))

theorem complete_10_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 10 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_2_0_6 plane_2_0_8 282797744028 94168568283 275461549151
      (by decide) p (plane_0_10_17_sound p h0) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_10_10 plane_2_1_9 289889229815 188469167116 289027502998
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_10_10_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_10_10 plane_2_2_10 150324095006 95728368055 144513751499
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_10_10_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_12 plane_1_10_10 plane_2_3_6 33029106456 478928692456 562892190155
      (by decide) p (plane_0_10_12_sound p h0) (plane_1_10_10_sound p h1) (plane_2_3_6_sound p h2))
  · exact complete_10_10_4 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_10_13 plane_0_10_17 plane_2_5_13 97785562203 52496582228 146115791345
      (by decide) p (plane_0_10_13_sound p h0) (plane_0_10_17_sound p h0) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_13 plane_1_10_13 plane_2_6_9 118244314584 160754094625 108904366337
      (by decide) p (plane_0_10_13_sound p h0) (plane_1_10_13_sound p h1) (plane_2_6_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_7_6 plane_2_7_15 53402669690 57296139377 43986466857
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_7_6_sound p h2) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_10_17 plane_2_8_8 plane_2_8_13 90658323513 70761576674 63443117992
      (by decide) p (plane_1_10_17_sound p h1) (plane_2_8_8_sound p h2) (plane_2_8_13_sound p h2))
  · exact complete_10_10_9 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_1_10_13 plane_2_10_13 29561078646 13124145557 35461098799
      (by decide) p (plane_0_10_10_sound p h0) (plane_1_10_13_sound p h1) (plane_2_10_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_2_11_13 plane_2_11_19 47454416215 24160503512 2550867439
      (by decide) p (plane_1_10_10_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_10_10 plane_1_10_12 plane_2_12_12 31598666101 252961440741 564051211055
      (by decide) p (plane_1_10_10_sound p h1) (plane_1_10_12_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_10_13 plane_1_10_18 plane_2_13_13 296610908583 112605307394 283358547227
      (by decide) p (plane_1_10_13_sound p h1) (plane_1_10_18_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_10_12 plane_1_10_18 plane_2_14_14 286058466951 28422632345 556142498998
      (by decide) p (plane_1_10_12_sound p h1) (plane_1_10_18_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_15_15 plane_2_15_17 282797744028 3615241625 145011768897
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2))

theorem complete_10_12 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 12)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 12 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_2_0_6 plane_2_0_8 282797744028 94168568283 275461549151
      (by decide) p (plane_0_10_17_sound p h0) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_17 plane_2_1_9 188469167116 289994215265 280092222898
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_17_sound p h0) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_17 plane_2_2_10 95728368055 150282144431 140046111449
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_17_sound p h0) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_12_12 plane_1_12_19 plane_2_3_6 701296181064 56954921416 711055526561
      (by decide) p (plane_1_12_12_sound p h1) (plane_1_12_19_sound p h1) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_12_18 plane_2_4_10 plane_2_4_12 561792632189 48652965083 1044483374653
      (by decide) p (plane_1_12_18_sound p h1) (plane_2_4_10_sound p h2) (plane_2_4_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_1_12_18 plane_2_5_13 3934394987 15474998134 28017661439
      (by decide) p (plane_0_10_10_sound p h0) (plane_1_12_18_sound p h1) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_12_12 plane_1_12_18 plane_2_6_8 1044483374653 39328026361 452528907170
      (by decide) p (plane_1_12_12_sound p h1) (plane_1_12_18_sound p h1) (plane_2_6_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_12_12 plane_1_12_18 plane_2_7_9 1018382834983 31598666101 452528907170
      (by decide) p (plane_1_12_12_sound p h1) (plane_1_12_18_sound p h1) (plane_2_7_9_sound p h2))
  · exact complete_10_12_8 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_10_18 plane_1_12_17 plane_2_9_17 41390492312 296584132177 248405159872
      (by decide) p (plane_0_10_18_sound p h0) (plane_1_12_17_sound p h1) (plane_2_9_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_12_12 plane_2_10_13 plane_2_10_18 283358547227 249154618709 69220275977
      (by decide) p (plane_1_12_12_sound p h1) (plane_2_10_13_sound p h2) (plane_2_10_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_11_13 plane_2_11_19 94908832430 48337256299 551711303
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_19 plane_1_12_12 plane_2_12_12 214074416447 194526752133 265998687433
      (by decide) p (plane_0_10_19_sound p h0) (plane_1_12_12_sound p h1) (plane_2_12_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_19 plane_1_12_12 plane_2_13_12 157119495031 415576003437 265998687433
      (by decide) p (plane_0_10_19_sound p h0) (plane_1_12_12_sound p h1) (plane_2_13_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_11 plane_1_12_12 plane_2_14_16 3481536161 435484128809 208324689842
      (by decide) p (plane_0_10_11_sound p h0) (plane_1_12_12_sound p h1) (plane_2_14_16_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_2_15_15 plane_2_15_17 282797744028 3615241625 145011768897
      (by decide) p (plane_0_10_10_sound p h0) (plane_2_15_15_sound p h2) (plane_2_15_17_sound p h2))

theorem complete_10_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    (e1 : labels 1 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 13 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_2_0_8 148321889982 94168568283 144976325411
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_2_1_9 296610908583 188469167116 289952650822
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_2_2_10 153748074324 95728368055 144976325411
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_3_5 plane_2_3_11 452528907170 257938437109 60329575017
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_3_5_sound p h2) (plane_2_3_11_sound p h2))
  · exact complete_10_13_4 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_13_13 plane_2_5_13 150324095006 97785562203 144976325411
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_13_13_sound p h1) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_6_8 plane_2_6_14 144341116853 75162047503 3467060182
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_6_8_sound p h2) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_7_9 plane_2_7_19 1104672086663 589503107161 21657103543
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_7_9_sound p h2) (plane_2_7_19_sound p h2))
  · exact complete_10_13_8 labels p h e0 e1 he
  · exact complete_10_13_9 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_10_13 plane_2_10_18 283358547227 296610908583 112605307394
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_10_13_sound p h2) (plane_2_10_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_13_13 plane_2_11_13 plane_2_11_19 142363248645 74160944991 3467060182
      (by decide) p (plane_1_13_13_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_13_12 plane_1_13_16 plane_2_12_12 56954921416 157119495031 219550877952
      (by decide) p (plane_1_13_12_sound p h1) (plane_1_13_16_sound p h1) (plane_2_12_12_sound p h2))
  · exact complete_10_13_13 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_13_12 plane_1_13_13 plane_2_14_17 101720067329 194580865167 284027168089
      (by decide) p (plane_1_13_12_sound p h1) (plane_1_13_13_sound p h1) (plane_2_14_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_10_11 plane_1_13_13 plane_2_15_17 3015872044 545867118137 288312664489
      (by decide) p (plane_0_10_11_sound p h0) (plane_1_13_13_sound p h1) (plane_2_15_17_sound p h2))

theorem complete_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 10 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_1_0_6 plane_1_0_8 282797744028 4460421057 286489913177
      (by decide) p (plane_0_10_10_sound p h0) (plane_1_0_6_sound p h1) (plane_1_0_8_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_10_6 plane_0_10_12 plane_1_1_9 277886303201 4799263143 570154980917
      (by decide) p (plane_0_10_6_sound p h0) (plane_0_10_12_sound p h0) (plane_1_1_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_17 plane_1_2_10 144976325411 2669356303 140046111449
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_17_sound p h0) (plane_1_2_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_1_3_4 plane_1_3_11 711055526561 21478273037 825366240474
      (by decide) p (plane_0_10_10_sound p h0) (plane_1_3_4_sound p h1) (plane_1_3_11_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_1_4_12 plane_1_4_13 90658323513 92989527540 78272381
      (by decide) p (plane_0_10_10_sound p h0) (plane_1_4_12_sound p h1) (plane_1_4_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_12 plane_1_5_13 5925180949 146364030 5937381169
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_12_sound p h0) (plane_1_5_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_13 plane_1_6_13 32940028859 148796686621 144488640871
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_13_sound p h0) (plane_1_6_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_10_10 plane_0_10_12 plane_1_7_15 549569533268 234817143 564051211055
      (by decide) p (plane_0_10_10_sound p h0) (plane_0_10_12_sound p h0) (plane_1_7_15_sound p h1))
  · exact complete_10_8 labels p h e0 he
  · exact complete_10_9 labels p h e0 he
  · exact complete_10_10 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_10_13 plane_1_11_13 plane_1_11_19 142363248645 70440797646 58992250217
      (by decide) p (plane_0_10_13_sound p h0) (plane_1_11_13_sound p h1) (plane_1_11_19_sound p h1))
  · exact complete_10_12 labels p h e0 he
  · exact complete_10_13 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_14_14 plane_1_14_17 139669658299 41766690707 141095471221
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_14_14_sound p h1) (plane_1_14_17_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_10_17 plane_1_15_15 plane_1_15_17 282797744028 181086258647 141060621963
      (by decide) p (plane_0_10_17_sound p h0) (plane_1_15_15_sound p h1) (plane_1_15_17_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_10
