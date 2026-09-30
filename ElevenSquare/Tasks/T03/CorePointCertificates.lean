import ElevenSquare.Tasks.T03.FiniteConvex

namespace ElevenSquare.Pending.T03
noncomputable section

theorem reflectedCore_convex (p : Point) (Q : Set Point) (hQ : Convex ℝ Q) :
    Convex ℝ {c | p-c ∈ Q} := by
  intro x hx y hy a b ha hb hab
  have h := hQ hx hy ha hb hab
  change a • (p-x)+b • (p-y) ∈ Q at h
  have he : a • (p-x)+b • (p-y) = p-(a • x+b • y) := by
    ext
    · change a*(p.1-x.1)+b*(p.1-y.1) = p.1-(a*x.1+b*y.1)
      calc
        a*(p.1-x.1)+b*(p.1-y.1) = (a+b)*p.1-(a*x.1+b*y.1) := by ring
        _ = p.1-(a*x.1+b*y.1) := by rw [hab]; ring
    · change a*(p.2-x.2)+b*(p.2-y.2) = p.2-(a*x.2+b*y.2)
      calc
        a*(p.2-x.2)+b*(p.2-y.2) = (a+b)*p.2-(a*x.2+b*y.2) := by ring
        _ = p.2-(a*x.2+b*y.2) := by rw [hab]; ring
  rwa [he] at h

theorem owned_of_hull_core (q : UnitSquare) (centers : List QPoint) (Q : Set Point)
    (p : Point) (hQ : Convex ℝ Q) (hfit : CoreFits Q q)
    (hc : q.center ∈ rationalHull centers)
    (hv : ∀ c ∈ centers, p-realPoint c ∈ Q) : OpenSquare q p := by
  have hsub : rationalHull centers ⊆ {c | p-c ∈ Q} := by
    apply convexHull_min _ (reflectedCore_convex p Q hQ)
    rintro c ⟨v,hv',rfl⟩
    exact hv v hv'
  have h := hfit (p-q.center) (hsub hc)
  have he : q.center+(p-q.center) = p := by ext <;> simp
  rwa [he] at h

def corePointCheck (core : List QPoint) (p : QPoint) :
    List QPoint → List Barycentric3 → Bool
  | [], [] => true
  | c::cs, w::ws => w.check core (p-c) && corePointCheck core p cs ws
  | _, _ => false

theorem corePointCheck_vertices (core : List QPoint) (p : QPoint)
    (centers : List QPoint) (ws : List Barycentric3)
    (h : corePointCheck core p centers ws = true) :
    ∀ c ∈ centers, realPoint p-realPoint c ∈ rationalHull core := by
  induction centers generalizing ws with
  | nil => simp
  | cons c cs ih =>
    cases ws with
    | nil => simp [corePointCheck] at h
    | cons w ws =>
      simp only [corePointCheck,Bool.and_eq_true] at h
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · have hm := w.mem_hull core (p-v) h.1
        simpa [realPoint] using hm
      · exact ih ws h.2 v hv

theorem corePointCheck_owned (core : List QPoint) (p : QPoint)
    (centers : List QPoint) (ws : List Barycentric3)
    (h : corePointCheck core p centers ws = true)
    (q : UnitSquare) (hfit : CoreFits (rationalHull core) q)
    (hc : q.center ∈ rationalHull centers) : OpenSquare q (realPoint p) :=
  owned_of_hull_core q centers (rationalHull core) (realPoint p)
    (convex_convexHull ℝ _) hfit hc (corePointCheck_vertices core p centers ws h)

end
end ElevenSquare.Pending.T03
