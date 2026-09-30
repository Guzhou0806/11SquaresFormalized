import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCoverage
import ElevenSquare.Tasks.T01.Handoff.Groups.G004.Support

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004
open ElevenSquare.Pending
noncomputable section

/-- Convert physical support cells to the five owners used by the support theorem. -/
def supportRole (cell : Fin 16) : Fin 5 :=
  if cell.val = 0 then 0 else if cell.val = 1 then 1 else
  if cell.val = 2 then 2 else if cell.val = 3 then 3 else 4

theorem supportRole_spec (cell : Fin 16) (hc : cell ∈ support) :
    supportCells (supportRole cell) = cell := by
  exact (by decide : ∀ c ∈ support, supportCells (supportRole c) = c) cell hc

theorem supportRole_ne (c d : Fin 16) (hc : c ∈ support) (hd : d ∈ support)
    (hne : c ≠ d) : supportRole c ≠ supportRole d := by
  intro he
  apply hne
  rw [← supportRole_spec c hc, ← supportRole_spec d hd, he]

def WindowCapture (c : Fin 5) (w : ℚ × ℚ) : Prop :=
  ∀ (P : Packing 11 coverCap), IsCharted P →
    ∀ (owners : Fin 5 → Owner), Function.Injective owners →
      (∀ d, ClosedCell (supportCells d)
        (normalizeCenter (P.squares (owners d)).center)) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (P.squares (owners c)).axis = chartAxis t →
        (w.1 : ℝ) ≤ t → t ≤ (w.2 : ℝ) →
        BaselineMajorityCapture featureSites 3 (P.squares (owners c))

theorem capture_of_windows (c : Fin 5) (windows : List (ℚ × ℚ))
    (hcover : ClosedWindowCoverCheck windows)
    (hw : ∀ w ∈ windows, WindowCapture c w)
    (P : Packing 11 coverCap) (hc : IsCharted P)
    (owners : Fin 5 → Owner) (hinj : Function.Injective owners)
    (hcell : ∀ d, ClosedCell (supportCells d)
      (normalizeCenter (P.squares (owners d)).center)) :
    BaselineMajorityCapture featureSites 3 (P.squares (owners c)) := by
  obtain ⟨t, ht0, ht1, ha⟩ := hc (owners c)
  exact closed_window_cover_sound windows hcover
    (fun u => 0 ≤ u → u ≤ 1 → (P.squares (owners c)).axis = chartAxis u →
      BaselineMajorityCapture featureSites 3 (P.squares (owners c)))
    (fun w hmem u hlu huu hu0 hu1 hau =>
      hw w hmem P hc owners hinj hcell u hu0 hu1 hau hlu huu)
    t ht0 ht1 ht0 ht1 ha

theorem support_capture_of_fixed_windows
    (h1 : ∀ w ∈ fixedCell01Windows, WindowCapture 1 w)
    (h2 : ∀ w ∈ fixedCell02Windows, WindowCapture 2 w) :
    SupportCapture := by
  intro P hc owners hinj hcell
  exact ⟨capture_of_windows 1 _ fixedCell01_windows_checked h1 P hc owners hinj hcell,
    capture_of_windows 2 _ fixedCell02_windows_checked h2 P hc owners hinj hcell⟩

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.support_capture_of_fixed_windows
