import ElevenSquare.Tasks.T03.DifferenceCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

def differenceHullCheck (ks qs : List QPoint) :
    List QPoint → List (QPoint × QPoint) → Bool
  | [], [] => true
  | p::ps, (k,v)::ws => differenceCheck ks qs k v p && differenceHullCheck ks qs ps ws
  | _, _ => false

theorem differenceHullCheck_vertices (ks qs vs : List QPoint) (ws : List (QPoint × QPoint))
    (h : differenceHullCheck ks qs vs ws = true) :
    ∀ p ∈ vs, realPoint p ∈ forbiddenCenters (rationalHull ks) (rationalHull qs) := by
  induction vs generalizing ws with
  | nil => simp
  | cons p ps ih =>
    cases ws with
    | nil => simp [differenceHullCheck] at h
    | cons w ws =>
      obtain ⟨k,v⟩ := w
      simp only [differenceHullCheck,Bool.and_eq_true] at h
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact differenceCheck_sound ks qs k v r h.1
      · exact ih ws h.2 r hr

theorem differenceHullCheck_sound (ks qs vs : List QPoint) (ws : List (QPoint × QPoint))
    (h : differenceHullCheck ks qs vs ws = true) :
    rationalHull vs ⊆ forbiddenCenters (rationalHull ks) (rationalHull qs) := by
  apply convexHull_min _ (forbiddenCenters_convex _ _ (convex_convexHull ℝ _) (convex_convexHull ℝ _))
  rintro p ⟨v,hv,rfl⟩
  exact differenceHullCheck_vertices ks qs vs ws h v hv

end
end ElevenSquare.Pending.T03
