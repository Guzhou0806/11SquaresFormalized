import ElevenSquare.Pending.S07_CellHalfplanes
import Mathlib.Tactic.FinCases

/-! Exact rational halfplanes for the original closed Voronoi cells. -/
namespace ElevenSquare.Pending
noncomputable section

def rationalCoverSite (i : Fin 16) : QPoint :=
(![((104991 / 1000000), (265837 / 2000000)),
    ((186601 / 500000), (45503 / 1000000)),
    ((1267243 / 2000000), (34689 / 250000)),
    ((1731123 / 2000000), (25701 / 250000)),
    ((206181 / 2000000), (400379 / 1000000)),
    ((742311 / 2000000), (312933 / 1000000)),
    ((635257 / 1000000), (166409 / 400000)),
    ((445439 / 500000), (167763 / 500000)),
    ((54561 / 500000), (332237 / 500000)),
    ((364743 / 1000000), (233591 / 400000)),
    ((1257689 / 2000000), (687067 / 1000000)),
    ((1793819 / 2000000), (599621 / 1000000)),
    ((268877 / 2000000), (224299 / 250000)),
    ((732757 / 2000000), (215311 / 250000)),
    ((313399 / 500000), (954497 / 1000000)),
    ((895009 / 1000000), (1734163 / 2000000))] : Fin 16 → QPoint) i

theorem rationalCoverSite_correct (i : Fin 16) :
    realPoint (rationalCoverSite i) = coverSite i := by
  fin_cases i <;> norm_num [rationalCoverSite, coverSite, realPoint]

def bisectorPlane (a b : QPoint) : Halfplane :=
  ⟨2*(b.1-a.1), 2*(b.2-a.2), b.1*b.1+b.2*b.2-a.1*a.1-a.2*a.2⟩

theorem bisectorPlane_correct (a b : QPoint) (p : Point) :
    (bisectorPlane a b).contains p ↔
      coordinateDistanceSq p (realPoint a) ≤ coordinateDistanceSq p (realPoint b) := by
  rw [distance_comparison_linear]
  simp [bisectorPlane, Halfplane.contains, realPoint, pow_two]

def unitBoxPlanes : Polygon :=
  [⟨-1,0,0⟩, ⟨1,0,1⟩, ⟨0,-1,0⟩, ⟨0,1,1⟩]

theorem unitBoxPlanes_correct (p : Point) :
    p ∈ unitBoxPlanes.carrier ↔ InUnitBox p := by
  simp [Polygon.carrier, unitBoxPlanes, Halfplane.contains, InUnitBox]

def cellPlanes (i : Fin 16) : Polygon :=
  unitBoxPlanes ++ (List.finRange 16).map
    (fun j => bisectorPlane (rationalCoverSite i) (rationalCoverSite j))

theorem cellPlanes_correct (i : Fin 16) (p : Point) :
    p ∈ (cellPlanes i).carrier ↔ ClosedCell i p := by
  constructor
  · intro h
    refine ⟨(unitBoxPlanes_correct p).mp ?_, ?_⟩
    · intro l hl
      exact h l (List.mem_append.mpr (Or.inl hl))
    · intro j
      rw [← rationalCoverSite_correct i, ← rationalCoverSite_correct j]
      apply (bisectorPlane_correct _ _ p).mp
      exact h _ (List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)))
  · intro h l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact (unitBoxPlanes_correct p).mpr h.1 l hl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hl
      apply (bisectorPlane_correct _ _ p).mpr
      rw [rationalCoverSite_correct, rationalCoverSite_correct]
      exact h.2 j

end
end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.rationalCoverSite_correct
#print axioms ElevenSquare.Pending.cellPlanes_correct
