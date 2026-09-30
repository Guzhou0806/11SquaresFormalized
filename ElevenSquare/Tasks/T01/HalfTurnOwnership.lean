import ElevenSquare.Tasks.T01.HalfTurnPacking
import ElevenSquare.Tasks.T01.Wall

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- Exact reflection of a rational owned point about the container centre. -/
def reflectQPoint (p : QPoint) : QPoint :=
  (baselineRationalCap-p.1, baselineRationalCap-p.2)

theorem realPoint_reflectQPoint (p : QPoint) :
    realPoint (reflectQPoint p) = reflectPoint coverCap (realPoint p) := by
  ext <;> simp [realPoint, reflectQPoint, reflectPoint, baselineRationalCap_cast]

theorem turnedSquare_contained (q : UnitSquare)
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p) :
    ∀ p, ClosedSquare (turnedSquare coverCap q) p → InContainer coverCap p := by
  intro p hp
  have h := hcont (reflectPoint coverCap p) ((turnedSquare_closed coverCap q p).mp hp)
  rcases h with ⟨hx0,hx1,hy0,hy1⟩
  dsimp [reflectPoint] at hx0 hx1 hy0 hy1
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A half-turn preserves the chart, so ownership for a reflected point in
one cell proves ownership in the opposite cell at the same orientation. -/
theorem point_owned_of_halfTurn (cell : Fin 16) (p : QPoint)
    (howned : ∀ q : UnitSquare,
      ClosedCell cell (normalizeCenter q.center) →
      (∀ x, ClosedSquare q x → InContainer coverCap x) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      OpenSquare q (realPoint (reflectQPoint p)))
    (q : UnitSquare) (hcell : ClosedCell cell.rev (normalizeCenter q.center))
    (hcont : ∀ x, ClosedSquare q x → InContainer coverCap x)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint p) := by
  have hc : ClosedCell cell (normalizeCenter (turnedSquare coverCap q).center) := by
    change ClosedCell cell (normalizeCenter (reflectPoint coverCap q.center))
    rw [normalize_reflectPoint]
    simpa using closedCell_halfTurn hcell
  have ho := howned (turnedSquare coverCap q) hc (turnedSquare_contained q hcont) hchart
  have ho' := (turnedSquare_open coverCap q (realPoint (reflectQPoint p))).mp ho
  simpa only [realPoint_reflectQPoint, reflectPoint_twice] using ho'

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.point_owned_of_halfTurn
