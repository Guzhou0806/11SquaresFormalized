import ElevenSquare.Pending.Types
import ElevenSquare.Cover
import ElevenSquare.Combinatorics
import ElevenSquare.Orientation

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

/-- Half-turn about the centre of the containing square. -/
def reflectPoint (S : ℝ) (p : Point) : Point := (S - p.1, S - p.2)

@[simp] theorem reflectPoint_twice (S : ℝ) (p : Point) :
    reflectPoint S (reflectPoint S p) = p := by
  ext <;> simp [reflectPoint]

/-- The axis can be kept unchanged: a square has central symmetry. This
preserves its chart parameter as well as its actual open and closed shape. -/
def turnedSquare (S : ℝ) (q : UnitSquare) : UnitSquare where
  center := reflectPoint S q.center
  axis := q.axis
  axis_unit := q.axis_unit

theorem turnedSquare_localX (S : ℝ) (q : UnitSquare) (p : Point) :
    localX (turnedSquare S q) p = -localX q (reflectPoint S p) := by
  dsimp [localX, turnedSquare, reflectPoint, dot]
  ring

theorem turnedSquare_localY (S : ℝ) (q : UnitSquare) (p : Point) :
    localY (turnedSquare S q) p = -localY q (reflectPoint S p) := by
  dsimp [localY, turnedSquare, reflectPoint, dot, perp]
  ring

theorem turnedSquare_closed (S : ℝ) (q : UnitSquare) (p : Point) :
    ClosedSquare (turnedSquare S q) p ↔ ClosedSquare q (reflectPoint S p) := by
  simp only [ClosedSquare, turnedSquare_localX, turnedSquare_localY, abs_neg]

theorem turnedSquare_open (S : ℝ) (q : UnitSquare) (p : Point) :
    OpenSquare (turnedSquare S q) p ↔ OpenSquare q (reflectPoint S p) := by
  simp only [OpenSquare, turnedSquare_localX, turnedSquare_localY, abs_neg]

def turnPacking {n : ℕ} {S : ℝ} (P : Packing n S) : Packing n S where
  squares := fun i => turnedSquare S (P.squares i)
  side_nonneg := P.side_nonneg
  contained := by
    intro i p hp
    have h := P.contained i (reflectPoint S p) ((turnedSquare_closed S _ p).mp hp)
    rcases h with ⟨hx0, hx1, hy0, hy1⟩
    dsimp [reflectPoint] at hx0 hx1 hy0 hy1
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  interior_disjoint := by
    intro i j hij p hp
    exact P.interior_disjoint i j hij (reflectPoint S p)
      ⟨(turnedSquare_open S _ p).mp hp.1, (turnedSquare_open S _ p).mp hp.2⟩

theorem turnPacking_charted {S : ℝ} (P : Packing 11 S) (hc : IsCharted P) :
    IsCharted (turnPacking P) := by
  intro i
  exact hc i

theorem normalize_reflectPoint (p : Point) :
    normalizeCenter (reflectPoint coverCap p) = turnPoint (normalizeCenter p) := by
  have hd : coverCap - 1 ≠ 0 := ne_of_gt (sub_pos.mpr coverCap_gt_one)
  apply Prod.ext <;> dsimp [normalizeCenter, reflectPoint, turnPoint]
  all_goals field_simp [hd] <;> ring

theorem turnPacking_occupies (P : Packing 11 coverCap) (m : CellMask)
    (hm : Occupies P m) : Occupies (turnPacking P) (halfTurnMask m) := by
  obtain ⟨a, ha, hmask, hcell⟩ := hm
  refine ⟨fun i => (a i).rev, ?_, ?_, ?_⟩
  · intro i j h
    exact ha (Fin.rev_inj.mp h)
  · rw [halfTurnMask, ← hmask, Finset.image_image]
    rfl
  · intro i
    change ClosedCell (a i).rev (normalizeCenter (reflectPoint coverCap (P.squares i).center))
    rw [normalize_reflectPoint]
    exact closedCell_halfTurn (hcell i)

/-- A checked exclusion for one support also excludes its half-turn, without
adding any orientation or cell-interior assumptions. -/
theorem charted_exclusion_halfTurn (m : CellMask)
    (hex : ∀ P : Packing 11 coverCap, IsCharted P → Occupies P m → False)
    (P : Packing 11 coverCap) (hc : IsCharted P)
    (hm : Occupies P (halfTurnMask m)) : False := by
  apply hex (turnPacking P) (turnPacking_charted P hc)
  simpa only [halfTurnMask_twice] using turnPacking_occupies P (halfTurnMask m) hm

/-- A support certificate applies uniformly to every mask containing its
required cells, including masks with the required support after a half-turn. -/
theorem charted_exclusion_of_support_or_halfTurn (support m : CellMask)
    (hex : ∀ m' : CellMask, support ⊆ m' →
      ∀ P : Packing 11 coverCap, IsCharted P → Occupies P m' → False)
    (hs : support ⊆ m ∨ support ⊆ halfTurnMask m)
    (P : Packing 11 coverCap) (hc : IsCharted P) (hm : Occupies P m) : False := by
  rcases hs with hs | hs
  · exact hex m hs P hc hm
  · exact hex (halfTurnMask m) hs (turnPacking P)
      (turnPacking_charted P hc) (turnPacking_occupies P m hm)

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.turnPacking_occupies
#print axioms ElevenSquare.Tasks.T01.charted_exclusion_halfTurn
#print axioms ElevenSquare.Tasks.T01.charted_exclusion_of_support_or_halfTurn
