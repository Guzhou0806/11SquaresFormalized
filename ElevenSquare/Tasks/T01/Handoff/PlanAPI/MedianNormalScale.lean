import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianSupportFacet
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianSupportOrder

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending

/-- A rational normal perpendicular to the segment direction. -/
def pairNormal (d : QPoint) : QPoint := (d.2, -d.1)

def rationalScale (r : ℚ) (v : QPoint) : QPoint := (r*v.1, r*v.2)

theorem rational_dot_scaled (r : ℚ) (normal point : QPoint) :
    rationalDot (rationalScale r normal) point =
      r * rationalDot normal point := by
  dsimp [rationalDot, rationalScale]
  ring

theorem orthogonal_normal_is_scaled_pair_normal (d n : QPoint)
    (hd : d ≠ (0,0)) (hn : rationalDot n d = 0) :
    ∃ r : ℚ, n = rationalScale r (pairNormal d) := by
  by_cases hx : d.1 = 0
  · have hy : d.2 ≠ 0 := by
      intro hy
      apply hd
      exact Prod.ext hx hy
    refine ⟨n.1/d.2, ?_⟩
    have hn2 : n.2 = 0 := by
      dsimp [rationalDot] at hn
      rw [hx] at hn
      exact (mul_eq_zero.mp (by simpa [mul_comm] using hn)).resolve_right hy
    apply Prod.ext
    · dsimp [rationalScale, pairNormal]
      field_simp [hy]
    · simp [rationalScale, pairNormal, hx, hn2]
  · refine ⟨-n.2/d.1, ?_⟩
    apply Prod.ext
    · dsimp [rationalScale, pairNormal, rationalDot] at hn ⊢
      field_simp [hx]
      nlinarith [hn]
    · dsimp [rationalScale, pairNormal]
      field_simp [hx]

/-- Including both orientations of every site/core pair suffices: any
perpendicular rational facet normal is a nonnegative multiple of one of
those two rays. -/
theorem orthogonal_normal_is_nonneg_ray (d n : QPoint)
    (hd : d ≠ (0,0)) (hn : rationalDot n d = 0) :
    (∃ r : ℚ, 0 ≤ r ∧ n = rationalScale r (pairNormal d)) ∨
    (∃ r : ℚ, 0 ≤ r ∧ n = rationalScale r (pairNormal (qpointSubtract (0,0) d))) := by
  obtain ⟨r, hr⟩ := orthogonal_normal_is_scaled_pair_normal d n hd hn
  by_cases hp : 0 ≤ r
  · exact Or.inl ⟨r, hp, hr⟩
  · right
    have hrneg : r < 0 := lt_of_not_ge hp
    refine ⟨-r, (neg_pos.mpr hrneg).le, ?_⟩
    rw [hr]
    apply Prod.ext <;> simp [rationalScale, pairNormal, qpointSubtract]

/-- Multiplying a projection and its threshold by a positive rational leaves
the set counted below the median unchanged. This transports one finite-ray
median check to every positive multiple of that ray. -/
theorem median_lower_bound_scale_pos (sites : Finset QPoint) (k : ℕ)
    (projection : QPoint → ℚ) (b r : ℚ) (hr : 0 < r) :
    MedianLowerBound sites k (fun p => r * projection p) (r*b) ↔
      MedianLowerBound sites k projection b := by
  classical
  unfold MedianLowerBound
  have heq :
      sites.filter (fun p => r * projection p < r*b) =
        sites.filter (fun p => projection p < b) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hlt⟩
      exact ⟨hp, (mul_lt_mul_iff_of_pos_left hr).mp hlt⟩
    · rintro ⟨hp, hlt⟩
      exact ⟨hp, (mul_lt_mul_iff_of_pos_left hr).mpr hlt⟩
  rw [heq]

theorem median_lower_bound_zero (sites : Finset QPoint) (k : ℕ) :
    MedianLowerBound sites k (fun _ => (0:ℚ)) 0 ↔ 0 < k := by
  classical
  simp [MedianLowerBound]

end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.orthogonal_normal_is_nonneg_ray
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.median_lower_bound_scale_pos
