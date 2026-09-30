import ElevenSquare.Tasks.T01.Field03HybridCoverage
import ElevenSquare.Tasks.T01.Handoff.Groups.G003.Support

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G003
open ElevenSquare.Pending
noncomputable section

/-- A single closed angle window, with the four actual square owners retained. -/
def WindowCapture (c : Fin 4) (w : ℚ × ℚ) : Prop :=
  ∀ (P : Packing 11 coverCap), IsCharted P →
    ∀ (owners : Fin 4 → Owner), Function.Injective owners →
      (∀ d, ClosedCell (supportCells d) (normalizeCenter (P.squares (owners d)).center)) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (P.squares (owners c)).axis = chartAxis t →
        (w.1 : ℝ) ≤ t → t ≤ (w.2 : ℝ) →
        BaselineMajorityCapture baselineField03Sites 2 (P.squares (owners c))

/-- The finite hybrid chains suffice for the full geometric support theorem. -/
theorem support_capture_of_hybrid_windows
    (h4 : ∀ w ∈ field03Cell04HybridWindows, WindowCapture 1 w)
    (h8 : ∀ w ∈ field03Cell08HybridWindows, WindowCapture 2 w) :
    SupportCapture := by
  intro P hc owners hinj hcell
  constructor
  · obtain ⟨t, ht0, ht1, ha⟩ := hc (owners 1)
    exact field03_cell04_hybrid_coverage
      (fun u => 0 ≤ u → u ≤ 1 → (P.squares (owners 1)).axis = chartAxis u →
        BaselineMajorityCapture baselineField03Sites 2 (P.squares (owners 1)))
      (fun w hw u hlu huu hu0 hu1 hau =>
        h4 w hw P hc owners hinj hcell u hu0 hu1 hau hlu huu)
      t ht0 ht1 ht0 ht1 ha
  · obtain ⟨t, ht0, ht1, ha⟩ := hc (owners 2)
    exact field03_cell08_hybrid_coverage
      (fun u => 0 ≤ u → u ≤ 1 → (P.squares (owners 2)).axis = chartAxis u →
        BaselineMajorityCapture baselineField03Sites 2 (P.squares (owners 2)))
      (fun w hw u hlu huu hu0 hu1 hau =>
        h8 w hw P hc owners hinj hcell u hu0 hu1 hau hlu huu)
      t ht0 ht1 ht0 ht1 ha

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G003

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G003.support_capture_of_hybrid_windows
