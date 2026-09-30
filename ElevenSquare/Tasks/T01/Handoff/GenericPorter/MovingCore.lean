import ElevenSquare.Tasks.T01.Quadratic

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter
open ElevenSquare ElevenSquare.Pending
noncomputable section

/-- A point with local coordinates `(a,b)` in the frame of `q`. -/
def localOffset (q : UnitSquare) (a b : ℝ) : Point :=
  (a * q.axis.1 - b * q.axis.2, a * q.axis.2 + b * q.axis.1)

theorem localOffset_x (q : UnitSquare) (a b : ℝ) :
    localX q (q.center + localOffset q a b) = a := by
  have hu := q.axis_unit
  calc
    localX q (q.center + localOffset q a b) = a * normSq q.axis := by
      simp only [localX, add_sub_cancel_left, localOffset, dot, normSq,
        Prod.fst_add, Prod.snd_add]
      ring
    _ = a := by rw [hu]; ring

theorem localOffset_y (q : UnitSquare) (a b : ℝ) :
    localY q (q.center + localOffset q a b) = b := by
  have hu := q.axis_unit
  calc
    localY q (q.center + localOffset q a b) = b * normSq q.axis := by
      simp only [localY, add_sub_cancel_left, localOffset, dot, perp, normSq,
        Prod.fst_add, Prod.snd_add]
      ring
    _ = b := by rw [hu]; ring

theorem localOffset_strict_core (q : UnitSquare) (a b : ℝ)
    (ha : |a| < 1/2) (hb : |b| < 1/2) :
    OpenSquare q (q.center + localOffset q a b) := by
  simp only [OpenSquare, localOffset_x, localOffset_y]
  exact ⟨ha,hb⟩

/-- The local coordinates stay fixed while the world-space core turns with
    the square. -/
def movingCore (q : UnitSquare) (vs : List (ℝ × ℝ)) : Set Point :=
  convexHull ℝ {v | ∃ ab ∈ vs, v = localOffset q ab.1 ab.2}

theorem movingCore_fits (q : UnitSquare) (vs : List (ℝ × ℝ))
    (hv : ∀ ab ∈ vs, |ab.1| < 1/2 ∧ |ab.2| < 1/2) :
    ElevenSquare.Pending.CoreFits (movingCore q vs) q := by
  have hc := (openSquare_convex q).translate_preimage_right q.center
  have hh : movingCore q vs ⊆ {v | OpenSquare q (q.center + v)} := by
    apply convexHull_min _ hc
    rintro v ⟨ab, hab, rfl⟩
    exact localOffset_strict_core q ab.1 ab.2 (hv ab hab).1 (hv ab hab).2
  exact hh

/-- Rational-function world coordinates for a fixed local point. The
    numerator has degree at most two in the chart parameter. -/
def chartLocalOffset (a b t : ℝ) : Point :=
  ((a * (1-t^2) - 2*b*t)/(1+t^2),
   (2*a*t + b * (1-t^2))/(1+t^2))

theorem chartLocalOffset_eq (q : UnitSquare) (a b t : ℝ)
    (ha : q.axis = chartAxis t) :
    chartLocalOffset a b t = localOffset q a b := by
  simp only [chartLocalOffset, localOffset, ha, chartAxis]
  apply Prod.ext
  · simp only [Prod.fst]
    ring
  · simp only [Prod.snd]
    ring

theorem chartLocalOffset_strict_core (q : UnitSquare) (a b t : ℝ)
    (ha : q.axis = chartAxis t) (hx : |a| < 1/2) (hy : |b| < 1/2) :
    OpenSquare q (q.center + chartLocalOffset a b t) := by
  rw [chartLocalOffset_eq q a b t ha]
  exact localOffset_strict_core q a b hx hy

#print axioms localOffset_strict_core
#print axioms movingCore_fits
#print axioms chartLocalOffset_strict_core

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter
