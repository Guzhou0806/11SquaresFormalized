import ElevenSquare.BasicGeometry
import ElevenSquare.Tasks.T03.UniversalCollision
import ElevenSquare.Tasks.T03.CollisionFamily

namespace ElevenSquare.Pending.T03
noncomputable section

/-- An orientation-independent collision witness: the midpoint of the centers. -/
theorem overlap_of_center_distance_lt_one (q r : UnitSquare)
    (h : normSq (q.center - r.center) < 1) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  let p : Point := ((q.center.1 + r.center.1) / 2,
                    (q.center.2 + r.center.2) / 2)
  have hq : normSq (p - q.center) = normSq (q.center - r.center) / 4 := by
    dsimp [p, normSq, dot]
    ring
  have hr : normSq (p - r.center) = normSq (q.center - r.center) / 4 := by
    dsimp [p, normSq, dot]
    ring
  exact ⟨p, open_of_normSq_lt q p (by rw [hq]; linarith),
             open_of_normSq_lt r p (by rw [hr]; linarith)⟩

def unitCenterBall : Set Point := {p | normSq p < 1}

/-- Vertex tests extend to all centers, because the open unit disk is convex. -/
theorem unitCenterBall_convex : Convex ℝ unitCenterBall := by
  intro p hp q hq a b ha hb hab
  change normSq p < 1 at hp
  change normSq q < 1 at hq
  change normSq (a • p + b • q) < 1
  have hid : normSq (a • p + b • q) + a * b * normSq (p - q) =
      (a + b) * (a * normSq p + b * normSq q) := by
    dsimp [normSq, dot]
    ring
  rw [hab, one_mul] at hid
  have hnonneg : 0 ≤ a * b * normSq (p - q) :=
    mul_nonneg (mul_nonneg ha hb) (normSq_nonneg _)
  have hweight : a * normSq p + b * normSq q < 1 := by
    by_cases hz : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [hz, hb1] using hq
    · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
      calc
        a * normSq p + b * normSq q < a * 1 + b * 1 :=
          add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hp hpos)
            (mul_le_mul_of_nonneg_left (le_of_lt hq) hb)
        _ = 1 := by simpa using hab
  linarith

theorem hull_center_distance_overlap (xs ys : List QPoint)
    (h : ∀ x ∈ xs, ∀ y ∈ ys, normSq (realPoint x - realPoint y) < 1)
    (q r : UnitSquare) (hx : q.center ∈ rationalHull xs)
    (hy : r.center ∈ rationalHull ys) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  exact overlap_of_center_distance_lt_one q r
    (hull_difference_mem xs ys unitCenterBall unitCenterBall_convex h
      q.center hx r.center hy)

/-- Strict squared-distance comparison using only integer arithmetic. -/
def homDistanceCheck (p q : HomPoint) : Bool :=
  let x : ℤ := p.x * q.denominator - q.x * p.denominator
  let y : ℤ := p.y * q.denominator - q.y * p.denominator
  let d : ℤ := (p.denominator : ℤ) * q.denominator
  decide (0 < p.denominator ∧ 0 < q.denominator ∧ x * x + y * y < d * d)

theorem homDistanceCheck_sound (p q : HomPoint) (h : homDistanceCheck p q = true) :
    normSq (realPoint p.point - realPoint q.point) < 1 := by
  dsimp [homDistanceCheck] at h
  obtain ⟨hp, hq, hxy⟩ := of_decide_eq_true h
  have hp' : (0 : ℝ) < p.denominator := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q.denominator := by exact_mod_cast hq
  have hp0 := ne_of_gt hp'
  have hq0 := ne_of_gt hq'
  let X : ℝ := (p.x : ℝ) * q.denominator - (q.x : ℝ) * p.denominator
  let Y : ℝ := (p.y : ℝ) * q.denominator - (q.y : ℝ) * p.denominator
  let D : ℝ := (p.denominator : ℝ) * q.denominator
  have hd : 0 < D := mul_pos hp' hq'
  have hw : X * X + Y * Y < D * D := by
    dsimp [X, Y, D]
    exact_mod_cast hxy
  have he : normSq (realPoint p.point - realPoint q.point) =
      (X * X + Y * Y) / (D * D) := by
    dsimp [normSq, dot, realPoint, HomPoint.point, X, Y, D]
    push_cast
    field_simp [hp0, hq0]
    <;> ring
  rw [he]
  exact (div_lt_iff (mul_pos hd hd)).mpr (by simpa using hw)

def homUnitDistanceCheck (xs ys : List HomPoint) : Bool :=
  xs.all (fun p => ys.all (fun q => homDistanceCheck p q))

theorem homUnitDistanceCheck_sound (xs ys : List HomPoint)
    (h : homUnitDistanceCheck xs ys = true) (q r : UnitSquare)
    (hx : q.center ∈ rationalHull (xs.map HomPoint.point))
    (hy : r.center ∈ rationalHull (ys.map HomPoint.point)) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  simp only [homUnitDistanceCheck, List.all_eq_true] at h
  apply hull_center_distance_overlap (xs.map HomPoint.point) (ys.map HomPoint.point) _ q r hx hy
  intro x hx y hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
  exact homDistanceCheck_sound p s (h p hp s hs)

/-- This band needs no angle bounds or strict-core Minkowski construction. -/
def CollisionBand.ofUnitDistance {qi : List QPoint} {xs : List HomPoint}
    (band : PartnerBand) (h : homUnitDistanceCheck xs band.centers = true) :
    CollisionBand qi xs where
  row := band.row
  collision := by
    intro q r _ hx hr
    exact homUnitDistanceCheck_sound xs band.centers h q r hx (band.sound r hr).1

#print axioms overlap_of_center_distance_lt_one
#print axioms unitCenterBall_convex
#print axioms hull_center_distance_overlap
#print axioms homDistanceCheck_sound
#print axioms homUnitDistanceCheck_sound
#print axioms CollisionBand.ofUnitDistance

end
end ElevenSquare.Pending.T03
