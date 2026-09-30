import ElevenSquare.Tasks.T03.FiniteConvex
import ElevenSquare.Pending.S05_Trace

namespace ElevenSquare.Pending.T03
noncomputable section

/-- It suffices to check every pair of vertices, with no representative center
or angle substituted for a universally quantified partner pose. -/
theorem hull_difference_mem (xs ys : List QPoint) (M : Set Point) (hM : Convex ℝ M)
    (hv : ∀ x ∈ xs, ∀ y ∈ ys, realPoint x-realPoint y ∈ M) :
    ∀ x ∈ rationalHull xs, ∀ y ∈ rationalHull ys, x-y ∈ M := by
  have right (x : QPoint) (hx : x ∈ xs) :
      rationalHull ys ⊆ {y | realPoint x-y ∈ M} := by
    apply convexHull_min
    · rintro y ⟨v,hv',rfl⟩
      exact hv x hx v hv'
    · intro y hy z hz a b ha hb hab
      have hm := hM hy hz ha hb hab
      have he : realPoint x-(a • y+b • z) =
          a • (realPoint x-y)+b • (realPoint x-z) := by
        calc
          realPoint x-(a • y+b • z) = (a+b) • realPoint x-(a • y+b • z) := by
            rw [hab,one_smul]
          _ = a • (realPoint x-y)+b • (realPoint x-z) := by
            simp only [add_smul,smul_sub]
            abel
      change realPoint x-(a • y+b • z) ∈ M
      rw [he]
      exact hm
  intro x hx y hy
  have left : rationalHull xs ⊆ {x | x-y ∈ M} := by
    apply convexHull_min
    · rintro x ⟨v,hv',rfl⟩
      exact right v hv' hy
    · intro x hx z hz a b ha hb hab
      have hm := hM hx hz ha hb hab
      have he : (a • x+b • z)-y = a • (x-y)+b • (z-y) := by
        calc
          (a • x+b • z)-y = (a • x+b • z)-(a+b) • y := by rw [hab,one_smul]
          _ = a • (x-y)+b • (z-y) := by
            simp only [add_smul,smul_sub]
            abel
      change (a • x+b • z)-y ∈ M
      rw [he]
      exact hm
  exact left hx

def pointDifferenceCheck (x : QPoint) (ms : List QPoint) :
    List QPoint → List Barycentric3 → Bool
  | [], [] => true
  | y::ys, w::ws => w.check ms (x-y) && pointDifferenceCheck x ms ys ws
  | _, _ => false

theorem pointDifferenceCheck_sound (x : QPoint) (ms ys : List QPoint)
    (ws : List Barycentric3) (h : pointDifferenceCheck x ms ys ws = true) :
    ∀ y ∈ ys, realPoint x-realPoint y ∈ rationalHull ms := by
  induction ys generalizing ws with
  | nil => simp
  | cons y ys ih =>
    cases ws with
    | nil => simp [pointDifferenceCheck] at h
    | cons w ws =>
      simp only [pointDifferenceCheck,Bool.and_eq_true] at h
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simpa [realPoint] using w.mem_hull ms (x-z) h.1
      · exact ih ws h.2 z hz

def hullDifferenceCheck (ys ms : List QPoint) :
    List QPoint → List (List Barycentric3) → Bool
  | [], [] => true
  | x::xs, ws::rest => pointDifferenceCheck x ms ys ws && hullDifferenceCheck ys ms xs rest
  | _, _ => false

theorem hullDifferenceCheck_vertices (ys ms xs : List QPoint)
    (ws : List (List Barycentric3)) (h : hullDifferenceCheck ys ms xs ws = true) :
    ∀ x ∈ xs, ∀ y ∈ ys, realPoint x-realPoint y ∈ rationalHull ms := by
  induction xs generalizing ws with
  | nil => simp
  | cons x xs ih =>
    cases ws with
    | nil => simp [hullDifferenceCheck] at h
    | cons row rest =>
      simp only [hullDifferenceCheck,Bool.and_eq_true] at h
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact pointDifferenceCheck_sound z ms ys row h.1
      · exact ih rest h.2 z hz

theorem hullDifferenceCheck_sound (ys ms xs : List QPoint)
    (ws : List (List Barycentric3)) (h : hullDifferenceCheck ys ms xs ws = true) :
    ∀ x ∈ rationalHull xs, ∀ y ∈ rationalHull ys, x-y ∈ rationalHull ms :=
  hull_difference_mem xs ys (rationalHull ms) (convex_convexHull ℝ _)
    (hullDifferenceCheck_vertices ys ms xs ws h)

/-- Two strict cores overlap whenever the center difference has a checked
Minkowski witness. Closed difference regions are safe here. -/
theorem core_difference_overlap (q r : UnitSquare) (Qi Qj : Set Point)
    (hi : CoreFits Qi q) (hj : CoreFits Qj r)
    (h : q.center-r.center ∈ forbiddenCenters Qj Qi) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  obtain ⟨v,hv,u,hu,he⟩ := h
  refine ⟨r.center+v,?_,hj v hv⟩
  have hp := hi u hu
  have heq : q.center+u = r.center+v := by
    have hh : q.center-r.center=v-u := he
    ext
    · have h := congrArg Prod.fst hh
      dsimp at h ⊢
      linarith
    · have h := congrArg Prod.snd hh
      dsimp at h ⊢
      linarith
  exact heq ▸ hp

theorem universal_core_collision (rs : List PoseRow) (F : Set Point) (Qi : Set Point)
    (hpartner : ∀ r, RowsContain rs r → ∀ x ∈ F,
      ∃ Qj : Set Point, CoreFits Qj r ∧ x-r.center ∈ forbiddenCenters Qj Qi)
    (q r : UnitSquare) (hi : CoreFits Qi q) (hr : RowsContain rs r)
    (hc : q.center ∈ F) : ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  obtain ⟨Qj,hj,hm⟩ := hpartner r hr q.center hc
  exact core_difference_overlap q r Qi Qj hi hj hm

end
end ElevenSquare.Pending.T03
