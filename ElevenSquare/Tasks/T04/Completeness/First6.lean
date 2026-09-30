import ElevenSquare.Tasks.T04.Completeness.Planes0
import ElevenSquare.Tasks.T04.Completeness.Planes1
import ElevenSquare.Tasks.T04.Completeness.Planes2
import ElevenSquare.Tasks.T04.Completeness.Planes3
import ElevenSquare.Tasks.T04.LabelLookup

/-! Exhaustive independent closed-label choices beginning with 6.
Rejected extensions carry exact nonnegative original-halfplane certificates. -/
namespace ElevenSquare.Pending.T04Completeness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem complete_6_4_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 4)
    (e2 : labels 2 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 4 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 10 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_4_10 plane_3_0_8 6345271797 148321889982 295155055633
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_4_10_sound p h1) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_4_10 plane_3_1_9 12377849851 296610908583 590310111266
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_4_10_sound p h1) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_4_10 plane_3_2_10 10415553607 153748074324 295155055633
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_4_10_sound p h1) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_10 plane_3_3_11 plane_3_3_16 761038527496 1506608386910 68452719217
      (by decide) p (plane_1_4_10_sound p h1) (plane_3_3_11_sound p h3) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_4_10 plane_3_4_12 29364529509 292859327197 590310111266
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_4_10_sound p h1) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_4_10 plane_3_5_13 1655133909 150324095006 295155055633
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_4_10_sound p h1) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_10 plane_3_6_13 plane_3_6_14 144488640871 1655133909 282662169077
      (by decide) p (plane_1_4_10_sound p h1) (plane_3_6_13_sound p h3) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_10 plane_3_7_15 plane_3_7_17 566754254278 1083587974535 29364529509
      (by decide) p (plane_1_4_10_sound p h1) (plane_3_7_15_sound p h3) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_11 plane_1_4_9 plane_3_8_13 302248561216 235449636515 175725312954
      (by decide) p (plane_0_6_11_sound p h0) (plane_1_4_9_sound p h1) (plane_3_8_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_4_9 plane_1_4_13 plane_3_9_17 102667292328 47614852103 144193592835
      (by decide) p (plane_1_4_9_sound p h1) (plane_1_4_13_sound p h1) (plane_3_9_17_sound p h3))
  · refine ⟨(75 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row75]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_4_12 plane_3_11_13 plane_3_11_19 189817664860 94164690509 9788176503
      (by decide) p (plane_1_4_12_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_10_18 plane_3_12_17 248405159872 41390492312 296584132177
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_10_18_sound p h2) (plane_3_12_17_sound p h3))
  · refine ⟨(76 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row76]
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

theorem complete_6_5_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 6 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_3_0_6 plane_3_0_8 141398872014 5195400765 281228124047
      (by decide) p (plane_0_6_8_sound p h0) (plane_3_0_6_sound p h3) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_6_6 plane_3_1_9 27377711 15262853435 15823588948
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_6_6_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_1_5_13 plane_3_2_10 150282144431 6934120364 288280977931
      (by decide) p (plane_0_6_8_sound p h0) (plane_1_5_13_sound p h1) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_6_14 plane_3_3_5 28017661439 2605024337 15457684384
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_6_14_sound p h2) (plane_3_3_5_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_0_6_9 plane_3_4_13 100351480326 100955561673 146115791345
      (by decide) p (plane_0_6_6_sound p h0) (plane_0_6_9_sound p h0) (plane_3_4_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_9 plane_1_5_13 plane_3_5_13 7737499067 3119515037 7465494484
      (by decide) p (plane_0_6_9_sound p h0) (plane_1_5_13_sound p h1) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_10 plane_1_5_13 plane_3_6_13 94515900045 108257512397 144488640871
      (by decide) p (plane_1_5_10_sound p h1) (plane_1_5_13_sound p h1) (plane_3_6_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_3_7_9 plane_3_7_19 1104672086663 576194818729 11163951429
      (by decide) p (plane_1_5_13_sound p h1) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_6_14 plane_3_8_13 279203399763 90948203851 300564288862
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_6_14_sound p h2) (plane_3_8_13_sound p h3))
  · refine ⟨(77 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row77]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_6_14 plane_3_10_13 1866373621 690744503 1932210548
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_6_14_sound p h2) (plane_3_10_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_3_11_13 plane_3_11_19 94908832430 48337256299 551711303
      (by decide) p (plane_1_5_13_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_6_14 plane_3_12_12 1130435423 13245405489 15457684384
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_6_14_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_6_14 plane_3_13_13 157020959 9044004372 8840126143
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_6_14_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_6_14 plane_3_14_14 9078349777 296610908583 300564288862
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_6_14_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_14 plane_3_15_15 plane_3_15_17 282797744028 286489913177 4460421057
      (by decide) p (plane_2_6_14_sound p h2) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_6_5_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 5)
    (e2 : labels 2 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 10 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_2_10_10 plane_3_0_6 plane_3_0_8 282797744028 4460421057 286489913177
      (by decide) p (plane_2_10_10_sound p h2) (plane_3_0_6_sound p h3) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_10_10 plane_3_1_9 477807883 15262853435 15457684384
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_10_10_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_10_10 plane_3_2_10 8264261 465269797 454637776
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_10_10_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_10_10 plane_3_3_11 plane_3_3_16 58541425192 62541817438 1652174849
      (by decide) p (plane_2_10_10_sound p h2) (plane_3_3_11_sound p h3) (plane_3_3_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_10_10 plane_3_4_10 plane_3_4_12 561792632189 234817143 576561955862
      (by decide) p (plane_2_10_10_sound p h2) (plane_3_4_10_sound p h3) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_10_10 plane_3_5_13 19258425 407236793 406781168
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_10_10_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_10_10 plane_3_6_13 7831404559 4974521055 7728842192
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_10_10_sound p h2) (plane_3_6_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_10_10 plane_3_7_17 30638709769 30706594841 15457684384
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_10_10_sound p h2) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_0_6_11 plane_3_8_13 235449636515 90948203851 284027168089
      (by decide) p (plane_0_6_6_sound p h0) (plane_0_6_11_sound p h0) (plane_3_8_13_sound p h3))
  · refine ⟨(78 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row78]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_3_10_13 plane_3_10_17 146115791345 97785562203 52496582228
      (by decide) p (plane_1_5_13_sound p h1) (plane_3_10_13_sound p h3) (plane_3_10_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_3_11_13 plane_3_11_19 94908832430 48337256299 551711303
      (by decide) p (plane_1_5_13_sound p h1) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_10_18 plane_3_12_17 248405159872 41390492312 296584132177
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_10_18_sound p h2) (plane_3_12_17_sound p h3))
  · refine ⟨(79 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row79]
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

theorem complete_6_6_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 6)
    (e2 : labels 2 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 6 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_3_0_6 plane_3_0_8 141398872014 5195400765 281228124047
      (by decide) p (plane_0_6_8_sound p h0) (plane_3_0_6_sound p h3) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_2_6_6 plane_3_1_9 27377711 15262853435 15823588948
      (by decide) p (plane_1_6_14_sound p h1) (plane_2_6_6_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_0_6_14 plane_3_2_10 75162047503 3467060182 144341116853
      (by decide) p (plane_0_6_8_sound p h0) (plane_0_6_14_sound p h0) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_3_3_5 plane_3_3_11 452528907170 39328026361 1044483374653
      (by decide) p (plane_0_6_8_sound p h0) (plane_3_3_5_sound p h3) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_9 plane_1_6_9 plane_3_4_9 123563208361 159622266029 108904366337
      (by decide) p (plane_0_6_9_sound p h0) (plane_1_6_9_sound p h1) (plane_3_4_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_9 plane_0_6_13 plane_3_5_13 4609327155 3119515037 7604665309
      (by decide) p (plane_0_6_9_sound p h0) (plane_0_6_13_sound p h0) (plane_3_5_13_sound p h3))
  · refine ⟨(80 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row80]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_3_7_9 plane_3_7_19 1104672086663 576406739029 37825715679
      (by decide) p (plane_0_6_14_sound p h0) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_6_14 plane_3_8_13 279203399763 90948203851 300564288862
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_6_14_sound p h2) (plane_3_8_13_sound p h3))
  · refine ⟨(81 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row81]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_6_13 plane_3_10_10 plane_3_10_13 144488640871 108257512397 94515900045
      (by decide) p (plane_1_6_13_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_3_11_13 plane_3_11_19 47454416215 24160503512 2550867439
      (by decide) p (plane_0_6_14_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_2_6_14 plane_3_12_12 1130435423 13313760039 15474998134
      (by decide) p (plane_0_6_14_sound p h0) (plane_2_6_14_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_6_14 plane_3_13_13 2669356303 153758773765 150324095006
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_6_14_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_6_14 plane_3_14_14 9078349777 296584132177 300648190012
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_6_14_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_14 plane_3_15_15 plane_3_15_17 282797744028 286489913177 4460421057
      (by decide) p (plane_2_6_14_sound p h2) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_6_6_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 6)
    (e2 : labels 2 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 9 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_2_9_9 plane_3_0_6 plane_3_0_8 282797744028 4460421057 286489913177
      (by decide) p (plane_2_9_9_sound p h2) (plane_3_0_6_sound p h3) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_2_9_9 plane_3_1_9 477807883 15257327885 15474998134
      (by decide) p (plane_0_6_14_sound p h0) (plane_2_9_9_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_2_9_9 plane_3_2_10 140492437 7911794474 7737499067
      (by decide) p (plane_0_6_14_sound p h0) (plane_2_9_9_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_9_9 plane_3_3_5 plane_3_3_11 452528907170 21478273037 532335567341
      (by decide) p (plane_2_9_9_sound p h2) (plane_3_3_5_sound p h3) (plane_3_3_11_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_9_15 plane_3_4_9 plane_3_4_12 285288226896 562547462351 169369427726
      (by decide) p (plane_2_9_15_sound p h2) (plane_3_4_9_sound p h3) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_13 plane_2_9_10 plane_3_5_13 148796686621 87577215945 202773412442
      (by decide) p (plane_0_6_13_sound p h0) (plane_2_9_10_sound p h2) (plane_3_5_13_sound p h3))
  · refine ⟨(82 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row82]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_2_9_9 plane_3_7_10 14694915777 4248202933 15474998134
      (by decide) p (plane_0_6_14_sound p h0) (plane_2_9_9_sound p h2) (plane_3_7_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_9_15 plane_2_9_17 plane_3_8_13 282973951883 155354934215 590105431712
      (by decide) p (plane_2_9_15_sound p h2) (plane_2_9_17_sound p h2) (plane_3_8_13_sound p h3))
  · refine ⟨(83 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row83]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_1_6_13 plane_3_10_10 plane_3_10_13 144488640871 108257512397 94515900045
      (by decide) p (plane_1_6_13_sound p h1) (plane_3_10_10_sound p h3) (plane_3_10_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_2_9_17 plane_3_11_13 295155055633 15305204634 150282144431
      (by decide) p (plane_0_6_14_sound p h0) (plane_2_9_17_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_8 plane_1_6_14 plane_3_12_12 251662704291 68452719217 577364467412
      (by decide) p (plane_1_6_8_sound p h1) (plane_1_6_14_sound p h1) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_8 plane_3_13_13 plane_3_13_14 146115791345 273901749379 10415553607
      (by decide) p (plane_1_6_8_sound p h1) (plane_3_13_13_sound p h3) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_6 plane_2_9_17 plane_3_14_14 520176509 296584132177 307496148648
      (by decide) p (plane_1_6_6_sound p h1) (plane_2_9_17_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_6_8 plane_1_6_14 plane_3_15_15 145011768897 6345271797 288682233706
      (by decide) p (plane_1_6_8_sound p h1) (plane_1_6_14_sound p h1) (plane_3_15_15_sound p h3))

theorem complete_6_9_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 9)
    (e2 : labels 2 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 9 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 6 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_1_9_17 plane_3_0_8 148309456911 10390801530 295155055633
      (by decide) p (plane_0_6_8_sound p h0) (plane_1_9_17_sound p h1) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_6_6 plane_3_1_9 520176509 296584132177 307496148648
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_6_6_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_1_9_17 plane_3_2_10 153758773765 6934120364 295155055633
      (by decide) p (plane_0_6_8_sound p h0) (plane_1_9_17_sound p h1) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_0_6_14 plane_3_3_6 8257276614 123993113122 144341116853
      (by decide) p (plane_0_6_8_sound p h0) (plane_0_6_14_sound p h0) (plane_3_3_6_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_3_4_9 plane_3_4_12 285288226896 286171280935 101682896638
      (by decide) p (plane_1_9_9_sound p h1) (plane_3_4_9_sound p h3) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_13 plane_1_9_9 plane_3_5_13 7737499067 4609327155 7831404559
      (by decide) p (plane_0_6_13_sound p h0) (plane_1_9_9_sound p h1) (plane_3_5_13_sound p h3))
  · refine ⟨(84 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row84]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_3_7_9 plane_3_7_19 1104672086663 576406739029 37825715679
      (by decide) p (plane_0_6_14_sound p h0) (plane_3_7_9_sound p h3) (plane_3_7_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_6_14 plane_3_8_13 14694915777 4938379633 15457684384
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_6_14_sound p h2) (plane_3_8_13_sound p h3))
  · refine ⟨(85 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row85]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_2_6_13 plane_3_10_10 plane_3_10_13 144488640871 32940028859 148796686621
      (by decide) p (plane_2_6_13_sound p h2) (plane_3_10_10_sound p h3) (plane_3_10_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_3_11_13 plane_3_11_19 47454416215 24160503512 2550867439
      (by decide) p (plane_0_6_14_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_6_14 plane_3_12_12 21478273037 258269678195 300648190012
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_6_14_sound p h2) (plane_3_12_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_6_14 plane_3_13_13 157020959 9044004372 8840126143
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_6_14_sound p h2) (plane_3_13_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_6_14 plane_3_14_14 9078349777 296610908583 300564288862
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_6_14_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_6_14 plane_3_15_15 plane_3_15_17 282797744028 286489913177 4460421057
      (by decide) p (plane_2_6_14_sound p h2) (plane_3_15_15_sound p h3) (plane_3_15_17_sound p h3))

theorem complete_6_9_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 9)
    (e2 : labels 2 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_6_13 plane_2_9_10 plane_3_5_13 148796686621 87577215945 202773412442
      (by decide) p (plane_0_6_13_sound p h0) (plane_2_9_10_sound p h2) (plane_3_5_13_sound p h3))
  · refine ⟨(86 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row86]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_2_9_9 plane_3_7_10 14694915777 4248202933 15474998134
      (by decide) p (plane_0_6_14_sound p h0) (plane_2_9_9_sound p h2) (plane_3_7_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_9_17 plane_3_8_13 282973951883 93829213027 300648190012
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_9_17_sound p h2) (plane_3_8_13_sound p h3))
  · refine ⟨(87 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row87]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(88 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row88]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_2_9_17 plane_3_11_13 295155055633 15305204634 150282144431
      (by decide) p (plane_0_6_14_sound p h0) (plane_2_9_17_sound p h2) (plane_3_11_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_9_17 plane_3_12_17 3381599606 591153006 3955897237
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_9_17_sound p h2) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_9_14 plane_2_9_17 plane_3_13_14 144976325411 37885836517 146115791345
      (by decide) p (plane_2_9_14_sound p h2) (plane_2_9_17_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_9_17 plane_3_14_14 520176509 296610908583 307517547530
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_9_17_sound p h2) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_2_9_17 plane_3_15_17 293162151519 9944130700 150282144431
      (by decide) p (plane_0_6_14_sound p h0) (plane_2_9_17_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_6_9_10 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 9)
    (e2 : labels 2 = 10)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 9 (view 1 p) := by
    simpa only [e1] using h 1
  have h2 : ClosedCell 10 (view 2 p) := by
    simpa only [e2] using h 2
  generalize he : labels 3 = next
  have h3 := h 3
  rw [he] at h3
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_10_10 plane_3_0_8 4460421057 148309456911 150324095006
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_10_10_sound p h2) (plane_3_0_8_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_10_10 plane_3_1_9 9078349777 296584132177 300648190012
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_10_10_sound p h2) (plane_3_1_9_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_10_10 plane_3_2_10 2669356303 153758773765 150324095006
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_10_10_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_10_10 plane_3_3_14 67907427394 161609406436 75162047503
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_10_10_sound p h2) (plane_3_3_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_10_10 plane_3_4_10 15172683049 87112311 7728842192
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_10_10_sound p h2) (plane_3_4_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_10_10 plane_3_5_13 365910075 7909586549 7911794474
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_10_10_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_10_10 plane_2_10_13 plane_3_6_13 32940028859 148796686621 144488640871
      (by decide) p (plane_2_10_10_sound p h2) (plane_2_10_13_sound p h2) (plane_3_6_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_2_10_10 plane_3_7_14 15426735927 19705887317 15474998134
      (by decide) p (plane_0_6_14_sound p h0) (plane_2_10_10_sound p h2) (plane_3_7_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_10_18 plane_3_8_13 274101840469 93829213027 289889229815
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_10_18_sound p h2) (plane_3_8_13_sound p h3))
  · refine ⟨(89 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row89]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · refine ⟨(90 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row90]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_3_11_13 plane_3_11_19 47454416215 24160503512 2550867439
      (by decide) p (plane_0_6_14_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_10_18 plane_3_12_17 248405159872 44927628456 289889229815
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_10_18_sound p h2) (plane_3_12_17_sound p h3))
  · refine ⟨(91 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row91]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_1_9_8 plane_3_14_14 38851420011 57977845963 55793716524
      (by decide) p (plane_0_6_14_sound p h0) (plane_1_9_8_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_2_10_18 plane_3_15_17 113087766537 3977652280 57998843053
      (by decide) p (plane_0_6_14_sound p h0) (plane_2_10_18_sound p h2) (plane_3_15_17_sound p h3))

theorem complete_6_9_13 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 9)
    (e2 : labels 2 = 13)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
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
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_13_13 plane_3_2_10 1813877443 153748074324 153758773765
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_13_13_sound p h2) (plane_3_2_10_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_13_13 plane_3_3_14 32339065972 80804703218 38437018581
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_13_13_sound p h2) (plane_3_3_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_13_13 plane_3_4_12 8417041069 292859327197 307517547530
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_13_13_sound p h2) (plane_3_4_12_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_13_13 plane_3_5_13 157020959 8840126143 9044004372
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_13_13_sound p h2) (plane_3_5_13_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_17 plane_2_13_13 plane_3_6_14 157020959 8840126143 9044004372
      (by decide) p (plane_1_9_17_sound p h1) (plane_2_13_13_sound p h2) (plane_3_6_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_13 plane_3_7_15 plane_3_7_17 566754254278 578265315311 8417041069
      (by decide) p (plane_2_13_13_sound p h2) (plane_3_7_15_sound p h3) (plane_3_7_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_3_8_13 plane_3_8_16 246106080017 251662704291 93829213027
      (by decide) p (plane_1_9_9_sound p h1) (plane_3_8_13_sound p h3) (plane_3_8_16_sound p h3))
  · exact False.elim (refutationCheck_sound plane_2_13_14 plane_3_9_14 plane_3_9_17 146115791345 144976325411 37885836517
      (by decide) p (plane_2_13_14_sound p h2) (plane_3_9_14_sound p h3) (plane_3_9_17_sound p h3))
  · refine ⟨(92 : Fin 220), ?_⟩
    rw [T04LabelLookup.label_row92]
    funext g
    fin_cases g
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact he.symm
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_3_11_13 plane_3_11_19 47454416215 24160503512 2550867439
      (by decide) p (plane_0_6_14_sound p h0) (plane_3_11_13_sound p h3) (plane_3_11_19_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_4 plane_1_9_9 plane_3_12_17 7487938076 29353603808 48864511201
      (by decide) p (plane_1_9_4_sound p h1) (plane_1_9_9_sound p h1) (plane_3_12_17_sound p h3))
  · exact False.elim (refutationCheck_sound plane_1_9_8 plane_2_13_14 plane_3_13_14 20318017992 8154722029 22367449111
      (by decide) p (plane_1_9_8_sound p h1) (plane_2_13_14_sound p h2) (plane_3_13_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_1_9_8 plane_3_14_14 38851420011 57977845963 55793716524
      (by decide) p (plane_0_6_14_sound p h0) (plane_1_9_8_sound p h1) (plane_3_14_14_sound p h3))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_1_9_12 plane_3_15_17 28349296573 1046750600 14694915777
      (by decide) p (plane_0_6_14_sound p h0) (plane_1_9_12_sound p h1) (plane_3_15_17_sound p h3))

theorem complete_6_4 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 4)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 4 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_4_10 plane_2_0_6 plane_2_0_8 141398872014 5195400765 281228124047
      (by decide) p (plane_1_4_10_sound p h1) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_4_10 plane_2_1_9 21090479789 296584132177 590310111266
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_4_10_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_4_10 plane_2_2_10 6934120364 153758773765 295155055633
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_4_10_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_4_10 plane_1_4_12 plane_2_3_11 245232080481 39328026361 561792632189
      (by decide) p (plane_1_4_10_sound p h1) (plane_1_4_12_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_4_10 plane_2_4_10 plane_2_4_12 561792632189 3686431551 1131825858520
      (by decide) p (plane_1_4_10_sound p h1) (plane_2_4_10_sound p h2) (plane_2_4_12_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_4_10 plane_2_5_13 15305204634 150282144431 295155055633
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_4_10_sound p h1) (plane_2_5_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_4_10 plane_2_6_14 15305204634 150282144431 295155055633
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_4_10_sound p h1) (plane_2_6_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_4_10 plane_2_7_15 3686431551 292938243343 590310111266
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_4_10_sound p h1) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_4_10 plane_1_4_12 plane_2_8_14 11327968305 1104901880803 561792632189
      (by decide) p (plane_1_4_10_sound p h1) (plane_1_4_12_sound p h1) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_4_13 plane_2_9_14 plane_2_9_17 146115791345 100955561673 100351480326
      (by decide) p (plane_1_4_13_sound p h1) (plane_2_9_14_sound p h2) (plane_2_9_17_sound p h2))
  · exact complete_6_4_10 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_4_9 plane_2_11_13 plane_2_11_19 94908832430 15252595567 96015449549
      (by decide) p (plane_1_4_9_sound p h1) (plane_2_11_13_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_4_10 plane_1_4_12 plane_2_12_18 48652965083 1044483374653 561792632189
      (by decide) p (plane_1_4_10_sound p h1) (plane_1_4_12_sound p h1) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_15 plane_1_4_13 plane_2_13_14 22367449111 8154722029 21350669565
      (by decide) p (plane_0_6_15_sound p h0) (plane_1_4_13_sound p h1) (plane_2_13_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_11 plane_2_14_14 plane_2_14_17 139669658299 118124305790 44100614743
      (by decide) p (plane_0_6_11_sound p h0) (plane_2_14_14_sound p h2) (plane_2_14_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_0_6_11 plane_2_15_14 30598113403 28769887088 40575309727
      (by decide) p (plane_0_6_6_sound p h0) (plane_0_6_11_sound p h0) (plane_2_15_14_sound p h2))

theorem complete_6_5 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 5)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 5 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_1_5_13 plane_2_0_8 144963021072 6345271797 288280977931
      (by decide) p (plane_0_6_8_sound p h0) (plane_1_5_13_sound p h1) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_1_5_13 plane_2_1_9 289889229815 12377849851 576561955862
      (by decide) p (plane_0_6_8_sound p h0) (plane_1_5_13_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_1_5_13 plane_2_2_10 150324095006 10415553607 288280977931
      (by decide) p (plane_0_6_8_sound p h0) (plane_1_5_13_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_1_5_13 plane_2_3_11 252961440741 68452719217 576561955862
      (by decide) p (plane_0_6_8_sound p h0) (plane_1_5_13_sound p h1) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_4_4 plane_2_4_10 47454416215 2550867439 24160503512
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_4_4_sound p h2) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_13 plane_1_5_13 plane_2_5_10 59270785703 108257512397 148796686621
      (by decide) p (plane_0_6_13_sound p h0) (plane_1_5_13_sound p h1) (plane_2_5_10_sound p h2))
  · exact complete_6_5_6 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_6_9 plane_2_7_10 plane_2_7_15 271974970539 115273398799 236846182379
      (by decide) p (plane_0_6_9_sound p h0) (plane_2_7_10_sound p h2) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_8_4 plane_2_8_14 1104672086663 37825715679 576406739029
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_8_4_sound p h2) (plane_2_8_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_9_10 plane_2_9_14 7604665309 3119515037 4609327155
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_9_10_sound p h2) (plane_2_9_14_sound p h2))
  · exact complete_6_5_10 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_2_11_10 plane_2_11_14 144193592835 47614852103 102667292328
      (by decide) p (plane_0_6_6_sound p h0) (plane_2_11_10_sound p h2) (plane_2_11_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_5_13 plane_2_12_12 plane_2_12_18 452528907170 74753504753 252961440741
      (by decide) p (plane_1_5_13_sound p h1) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_5_8 plane_1_5_13 plane_2_13_14 10117034367 12250414744 16021510315
      (by decide) p (plane_1_5_8_sound p h1) (plane_1_5_13_sound p h1) (plane_2_13_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_11 plane_1_5_13 plane_2_14_14 289889229815 88201229486 279203399763
      (by decide) p (plane_0_6_11_sound p h0) (plane_1_5_13_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_0_6_11 plane_2_15_14 30598113403 28769887088 40575309727
      (by decide) p (plane_0_6_6_sound p h0) (plane_0_6_11_sound p h0) (plane_2_15_14_sound p h2))

theorem complete_6_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 6 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_0_6_14 plane_2_0_8 145011768897 6345271797 288682233706
      (by decide) p (plane_0_6_8_sound p h0) (plane_0_6_14_sound p h0) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_0_6_14 plane_2_1_9 289994215265 12377849851 577364467412
      (by decide) p (plane_0_6_8_sound p h0) (plane_0_6_14_sound p h0) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_0_6_14 plane_2_2_10 150282144431 10415553607 288682233706
      (by decide) p (plane_0_6_8_sound p h0) (plane_0_6_14_sound p h0) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_0_6_14 plane_2_3_11 251662704291 68452719217 577364467412
      (by decide) p (plane_0_6_8_sound p h0) (plane_0_6_14_sound p h0) (plane_2_3_11_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_0_6_14 plane_2_4_10 1655133909 566891805629 288682233706
      (by decide) p (plane_0_6_8_sound p h0) (plane_0_6_14_sound p h0) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_13 plane_2_5_10 plane_2_5_13 144488640871 94515900045 108257512397
      (by decide) p (plane_0_6_13_sound p h0) (plane_2_5_10_sound p h2) (plane_2_5_13_sound p h2))
  · exact complete_6_6_6 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_0_6_9 plane_2_7_10 plane_2_7_15 271974970539 115273398799 236846182379
      (by decide) p (plane_0_6_9_sound p h0) (plane_2_7_10_sound p h2) (plane_2_7_15_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_6_14 plane_2_8_8 plane_2_8_14 548479375832 37825715679 286480696885
      (by decide) p (plane_1_6_14_sound p h1) (plane_2_8_8_sound p h2) (plane_2_8_14_sound p h2))
  · exact complete_6_6_9 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_6_9 plane_2_10_10 plane_2_10_13 144488640871 118244314584 59270785703
      (by decide) p (plane_1_6_9_sound p h1) (plane_2_10_10_sound p h2) (plane_2_10_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_6_9 plane_2_11_10 16725246721 17111215388 24465033809
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_6_9_sound p h1) (plane_2_11_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_6_8 plane_2_12_12 plane_2_12_18 452528907170 1044483374653 39328026361
      (by decide) p (plane_1_6_8_sound p h1) (plane_2_12_12_sound p h2) (plane_2_12_18_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_6_8 plane_1_6_14 plane_2_13_13 75162047503 3467060182 144341116853
      (by decide) p (plane_1_6_8_sound p h1) (plane_1_6_14_sound p h1) (plane_2_13_13_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_6_8 plane_1_6_14 plane_2_14_14 289889229815 21090479789 577364467412
      (by decide) p (plane_1_6_8_sound p h1) (plane_1_6_14_sound p h1) (plane_2_14_14_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_6_8 plane_2_15_13 plane_2_15_15 28472649729 1039080153 55552212773
      (by decide) p (plane_1_6_8_sound p h1) (plane_2_15_13_sound p h2) (plane_2_15_15_sound p h2))

theorem complete_6_9 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    (e1 : labels 1 = 9)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  have h1 : ClosedCell 9 (view 1 p) := by
    simpa only [e1] using h 1
  generalize he : labels 2 = next
  have h2 := h 2
  rw [he] at h2
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_1_9_15 plane_2_0_6 plane_2_0_8 141398872014 5195400765 281228124047
      (by decide) p (plane_1_9_15_sound p h1) (plane_2_0_6_sound p h2) (plane_2_0_8_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_1_9_17 plane_2_1_9 296610908583 12377849851 590310111266
      (by decide) p (plane_0_6_8_sound p h0) (plane_1_9_17_sound p h1) (plane_2_1_9_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_1_9_17 plane_2_2_10 153748074324 10415553607 295155055633
      (by decide) p (plane_0_6_8_sound p h0) (plane_1_9_17_sound p h1) (plane_2_2_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_1_9_9 plane_2_3_6 16514553228 245736565796 288280977931
      (by decide) p (plane_0_6_8_sound p h0) (plane_1_9_9_sound p h1) (plane_2_3_6_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_1_9_15 plane_2_4_10 565912929260 1655133909 288280977931
      (by decide) p (plane_0_6_14_sound p h0) (plane_1_9_15_sound p h1) (plane_2_4_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_13 plane_2_5_10 plane_2_5_13 144488640871 94515900045 108257512397
      (by decide) p (plane_0_6_13_sound p h0) (plane_2_5_10_sound p h2) (plane_2_5_13_sound p h2))
  · exact complete_6_9_6 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_7_6 plane_2_7_10 284027168089 80715855727 219932334285
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_7_6_sound p h2) (plane_2_7_10_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_2_8_8 plane_2_8_14 548479375832 11163951429 286171280935
      (by decide) p (plane_0_6_14_sound p h0) (plane_2_8_8_sound p h2) (plane_2_8_14_sound p h2))
  · exact complete_6_9_9 labels p h e0 e1 he
  · exact complete_6_9_10 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_9_9 plane_2_11_10 plane_2_11_19 46887091617 48321007024 34294140193
      (by decide) p (plane_1_9_9_sound p h1) (plane_2_11_10_sound p h2) (plane_2_11_19_sound p h2))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_1_9_12 plane_2_12_17 75192966096 14975876152 93067799921
      (by decide) p (plane_0_6_14_sound p h0) (plane_1_9_12_sound p h1) (plane_2_12_17_sound p h2))
  · exact complete_6_9_13 labels p h e0 e1 he
  · exact False.elim (refutationCheck_sound plane_1_9_8 plane_2_14_14 plane_2_14_17 279339316598 204073209213 198540874785
      (by decide) p (plane_1_9_8_sound p h1) (plane_2_14_14_sound p h2) (plane_2_14_17_sound p h2))
  · exact False.elim (refutationCheck_sound plane_1_9_4 plane_1_9_9 plane_2_15_17 9944130700 269359545447 146593533603
      (by decide) p (plane_1_9_4_sound p h1) (plane_1_9_9_sound p h1) (plane_2_15_17_sound p h2))

theorem complete_6 (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p))
    (e0 : labels 0 = 6)
    : ∃ r : Fin 220, overlayLabels r = labels := by
  have h0 : ClosedCell 6 (view 0 p) := by
    simpa only [e0] using h 0
  generalize he : labels 1 = next
  have h1 := h 1
  rw [he] at h1
  fin_cases next
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_1_0_8 plane_1_0_9 143061215619 148185826108 179026671
      (by decide) p (plane_0_6_6_sound p h0) (plane_1_0_8_sound p h1) (plane_1_0_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_0_6_8 plane_1_1_9 569141090689 520176509 590105431712
      (by decide) p (plane_0_6_6_sound p h0) (plane_0_6_8_sound p h0) (plane_1_1_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_6_6 plane_0_6_9 plane_1_2_9 37885836517 144976325411 146115791345
      (by decide) p (plane_0_6_6_sound p h0) (plane_0_6_9_sound p h0) (plane_1_2_9_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_6_9 plane_0_6_14 plane_1_3_6 126193207060 28831203004 144488640871
      (by decide) p (plane_0_6_9_sound p h0) (plane_0_6_14_sound p h0) (plane_1_3_6_sound p h1))
  · exact complete_6_4 labels p h e0 he
  · exact complete_6_5 labels p h e0 he
  · exact complete_6_6 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_1_7_6 plane_1_7_10 284027168089 155354934215 434955177051
      (by decide) p (plane_0_6_8_sound p h0) (plane_1_7_6_sound p h1) (plane_1_7_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_6_15 plane_1_8_8 plane_1_8_13 30219441171 11497565201 31203773929
      (by decide) p (plane_0_6_15_sound p h0) (plane_1_8_8_sound p h1) (plane_1_8_13_sound p h1))
  · exact complete_6_9 labels p h e0 he
  · exact False.elim (refutationCheck_sound plane_0_6_13 plane_1_10_10 plane_1_10_13 144488640871 32940028859 148796686621
      (by decide) p (plane_0_6_13_sound p h0) (plane_1_10_10_sound p h1) (plane_1_10_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_0_6_14 plane_1_11_10 69742145655 101798132034 144341116853
      (by decide) p (plane_0_6_8_sound p h0) (plane_0_6_14_sound p h0) (plane_1_11_10_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_6_8 plane_0_6_14 plane_1_12_12 21478273037 496971563523 577364467412
      (by decide) p (plane_0_6_8_sound p h0) (plane_0_6_14_sound p h0) (plane_1_12_12_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_1_13_12 plane_1_13_13 284027168089 5338712606 273864687157
      (by decide) p (plane_0_6_14_sound p h0) (plane_1_13_12_sound p h1) (plane_1_13_13_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_1_14_14 plane_1_14_16 527155870326 532335567341 9078349777
      (by decide) p (plane_0_6_14_sound p h0) (plane_1_14_14_sound p h1) (plane_1_14_16_sound p h1))
  · exact False.elim (refutationCheck_sound plane_0_6_14 plane_1_15_13 plane_1_15_15 284726497290 4460421057 283820556874
      (by decide) p (plane_0_6_14_sound p h0) (plane_1_15_13_sound p h1) (plane_1_15_15_sound p h1))

end ElevenSquare.Pending.T04Completeness

#print axioms ElevenSquare.Pending.T04Completeness.complete_6
