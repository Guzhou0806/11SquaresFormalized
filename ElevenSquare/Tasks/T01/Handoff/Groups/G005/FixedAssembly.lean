import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCoverage
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.Support

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005
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


end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005
