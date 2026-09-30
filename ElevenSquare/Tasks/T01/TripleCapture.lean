import ElevenSquare.Tasks.T01.Majority

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

theorem pair_hull_toList (a b : QPoint) :
    rationalHull ({a,b} : Finset QPoint).toList = rationalHull [a,b] := by
  unfold rationalHull
  congr 1
  ext p
  simp

theorem pair_subset_triple (a b c : QPoint) (J : Finset QPoint)
    (hJ : J ∈ ({a,b,c} : Finset QPoint).powersetCard 2) :
    J = {a,b} ∨ J = {a,c} ∨ J = {b,c} := by
  classical
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hJ
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  have hx := hsub (show x ∈ ({x,y} : Finset QPoint) by simp)
  have hy := hsub (show y ∈ ({x,y} : Finset QPoint) by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals simp_all [Finset.pair_comm]

/-- For a three-point feature the three pair-capture obligations are complete. -/
theorem triple_majority_capture (a b c : QPoint) (q : UnitSquare)
    (hab : ∃ p ∈ rationalHull [a,b], OpenSquare q p)
    (hac : ∃ p ∈ rationalHull [a,c], OpenSquare q p)
    (hbc : ∃ p ∈ rationalHull [b,c], OpenSquare q p) :
    BaselineMajorityCapture {a,b,c} 2 q := by
  intro J hJ
  rcases pair_subset_triple a b c J hJ with rfl | rfl | rfl
  · simpa only [pair_hull_toList] using hab
  · simpa only [pair_hull_toList] using hac
  · simpa only [pair_hull_toList] using hbc

end
end ElevenSquare.Tasks.T01
