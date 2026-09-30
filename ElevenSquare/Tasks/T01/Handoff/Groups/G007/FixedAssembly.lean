import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCoverage
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Support

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending
noncomputable section

def WindowCapture (c : Fin 16) (w : ℚ × ℚ) : Prop :=
  ∀ (P : Packing 11 coverCap), IsCharted P →
    ∀ (owners : Fin 16 → Owner), SupportOwners P owners →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (P.squares (owners c)).axis = chartAxis t →
        (w.1 : ℝ) ≤ t → t ≤ (w.2 : ℝ) →
        CaptureChoice (P.squares (owners c))

theorem capture_of_windows (c : Fin 16) (windows : List (ℚ × ℚ))
    (hcover : ClosedWindowCoverCheck windows)
    (hw : ∀ w ∈ windows, WindowCapture c w)
    (P : Packing 11 coverCap) (hc : IsCharted P)
    (owners : Fin 16 → Owner) (hs : SupportOwners P owners) :
    CaptureChoice (P.squares (owners c)) := by
  obtain ⟨t, ht0, ht1, ha⟩ := hc (owners c)
  exact closed_window_cover_sound windows hcover
    (fun u => 0 ≤ u → u ≤ 1 → (P.squares (owners c)).axis = chartAxis u →
      CaptureChoice (P.squares (owners c)))
    (fun w hmem u hlu huu hu0 hu1 hau =>
      hw w hmem P hc owners hs u hu0 hu1 hau hlu huu)
    t ht0 ht1 ht0 ht1 ha

theorem support_capture_of_fixed_windows
    (h5 : ∀ w ∈ fixedCell05Windows, WindowCapture 5 w)
    (h9 : ∀ w ∈ fixedCell09Windows, WindowCapture 9 w)
    (h10 : ∀ w ∈ fixedCell10Windows, WindowCapture 10 w) :
    SupportCapture := by
  intro P hc owners hs j
  fin_cases j
  · exact capture_of_windows 5 _ fixedCell05_windows_checked h5 P hc owners hs
  · exact capture_of_windows 9 _ fixedCell09_windows_checked h9 P hc owners hs
  · exact capture_of_windows 10 _ fixedCell10_windows_checked h10 P hc owners hs

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.support_capture_of_fixed_windows
