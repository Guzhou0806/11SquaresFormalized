import ElevenSquare.Tasks.T07.GeometryAngles
import ElevenSquare.Tasks.T07.NearFinalPacket
import ElevenSquare.Tasks.T07.LocalAnglePacket

/-! The exact semantic handoff from case-438 trace ancestry to the focused
local packet. A final row records both the full closed angular interval and
the complete convex polygon containing the field center. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def FinalNearRowsHold (Q : Packing 11 coverCap) : Prop :=
  ∀ i : Owner, ∃ r ∈ nearRows i, ∃ t : ℝ,
    0 ≤ t ∧ t ≤ 1 ∧ (r.lo : ℝ) ≤ t ∧ t ≤ (r.hi : ℝ) ∧
    (Q.squares i).axis = chartAxis t ∧
    ∃ P ∈ r.polygons,
      toField (Q.squares i).center ∈ convexHull ℝ (nearPolygon P)

def nearOneBranch (i : Owner) (t : ℝ) : Bool :=
  decide (i.val < 6 ∧ 1/2 < t)

theorem quarterChart_low_angle (U V : ℝ) (q : UnitSquare) (t : ℝ)
    (haxis : q.axis = chartAxis t) :
    (quarterChartSquare U V q false).axis =
      rotateAxis (2*Real.arctan t) (1,0) := by
  rw [quarterChartSquare_axis_low U V q t haxis, chartAxis_trig]
  simp [rotateAxis]

theorem quarterChart_high_angle (U V : ℝ) (q : UnitSquare) (t : ℝ)
    (haxis : q.axis = chartAxis t) :
    (quarterChartSquare U V q true).axis =
      rotateAxis (2*Real.arctan t-Real.pi/2) (1,0) := by
  rw [show (quarterChartSquare U V q true).axis =
      ((chartAxis t).2,-(chartAxis t).1) by
        simp [quarterChartSquare, quarterSquare, haxis]]
  rw [chartAxis_trig]
  apply Prod.ext
  · simp [rotateAxis, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
  · simp [rotateAxis, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem quarterChart_tilt_angle (U V : ℝ) (q : UnitSquare) (t : ℝ)
    (haxis : q.axis = chartAxis t) :
    (quarterChartSquare U V q false).axis =
      rotateAxis (2*Real.arctan t-2*Real.arctan u) (chartAxis u) := by
  rw [quarterChartSquare_axis_low U V q t haxis]
  exact (chartAxis_rotate u t).symm

/-- The radian branch recorded by `LocalAnglePacket` is exactly the
orientation of the physical cap square after quarter-turn transport and a
shape-equivalent axis choice. -/
theorem near_quarterChart_rotates (i : Owner) (q : UnitSquare) (t : ℝ)
    (haxis : q.axis = chartAxis t) :
    (quarterChartSquare coverCap T q (nearOneBranch i t)).axis =
      rotateAxis (nearAngleDisplacement i t) (constructionSquare i).axis := by
  by_cases hi : i.val < 6
  · have hbase : (constructionSquare i).axis = (1,0) := by
      rw [construction_axis_chart]
      simp [hi, chartAxis]
    by_cases ht : t ≤ 1/2
    · have htInv : t ≤ (2 : ℝ)⁻¹ := by simpa only [one_div] using ht
      have hb : nearOneBranch i t = false := by
        simp [nearOneBranch, hi, not_lt.mpr htInv]
      have hθ : nearAngleDisplacement i t = 2*Real.arctan t := by
        simp [nearAngleDisplacement, hi, htInv]
      rw [hb, hθ, hbase]
      exact quarterChart_low_angle coverCap T q t haxis
    · have ht' : 1/2 < t := lt_of_not_ge ht
      have htInv : (2 : ℝ)⁻¹ < t := by simpa only [one_div] using ht'
      have hb : nearOneBranch i t = true := by
        simp [nearOneBranch, hi, htInv]
      have hθ : nearAngleDisplacement i t =
          2*Real.arctan t-Real.pi/2 := by
        simp [nearAngleDisplacement, hi, not_le.mpr htInv]
      rw [hb, hθ, hbase]
      exact quarterChart_high_angle coverCap T q t haxis
  · have hbase : (constructionSquare i).axis = chartAxis u := by
      rw [construction_axis_chart]
      simp [hi]
    simpa [nearOneBranch, nearAngleDisplacement, hi, hbase] using
      quarterChart_tilt_angle coverCap T q t haxis

/-- Every local coordinate has a unique role and one of three component
positions. Thus componentwise closed bounds imply the whole rectangle. -/
theorem poseWithAngles_inRectangle (q : Owner → UnitSquare) (θ : Owner → ℝ)
    (hcenter : ∀ i,
      |(q i).center.1-(constructionSquare i).center.1| ≤
        focusedRadii (coordinate i 0) ∧
      |(q i).center.2-(constructionSquare i).center.2| ≤
        focusedRadii (coordinate i 1))
    (hangle : ∀ i, |θ i| ≤ focusedRadii (coordinate i 2)) :
    InRectangle focusedRadii (poseDisplacementWithAngles q θ) := by
  intro j
  let i : Owner := ⟨j.val / 3, by omega⟩
  obtain ⟨k, hcoord⟩ : ∃ k : Fin 3, coordinate i k = j := by
    refine ⟨⟨j.val % 3, Nat.mod_lt _ (by decide)⟩, ?_⟩
    apply Fin.ext
    dsimp [coordinate, i]
    omega
  rw [← hcoord]
  fin_cases k
  · change |poseDisplacementWithAngles q θ (coordinate i 0)| ≤
        focusedRadii (coordinate i 0)
    rw [poseWithAngles_center_x]
    exact (hcenter i).1
  · change |poseDisplacementWithAngles q θ (coordinate i 1)| ≤
        focusedRadii (coordinate i 1)
    rw [poseWithAngles_center_y]
    exact (hcenter i).2
  · change |poseDisplacementWithAngles q θ (coordinate i 2)| ≤
        focusedRadii (coordinate i 2)
    rw [poseWithAngles_angle]
    exact hangle i

end
end ElevenSquare.Tasks.T07
