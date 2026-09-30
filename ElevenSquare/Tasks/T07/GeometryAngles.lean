import ElevenSquare.Tasks.T07.CoordinateBridge
import ElevenSquare.ConstructionData
import ElevenSquare.Pending.S08_GapDefinitions
import ElevenSquare.Pending.Types
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Construct the 33 local pose coordinates from physical centers and
rightward unit axes. The angular coordinate is in radians, as required
by the local packet. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def signedAngle (a : Point) : ℝ :=
  if 0 ≤ a.2 then Real.arccos a.1 else -Real.arccos a.1

theorem right_axis_trig (a : Point) (hu : normSq a = 1)
    (hx : 0 ≤ a.1) :
    a = (Real.cos (signedAngle a), Real.sin (signedAngle a)) := by
  have hbounds : -1 ≤ a.1 ∧ a.1 ≤ 1 := by
    dsimp [normSq, dot] at hu
    constructor <;> nlinarith [sq_nonneg a.2]
  have he : 1-a.1^2 = a.2^2 := by
    dsimp [normSq, dot] at hu
    nlinarith
  by_cases hy : 0 ≤ a.2
  · have hs : Real.sqrt (1-a.1^2) = a.2 := by rw [he, Real.sqrt_sq hy]
    apply Prod.ext
    · simpa [signedAngle, hy] using (Real.cos_arccos hbounds.1 hbounds.2).symm
    · simp [signedAngle, hy, Real.sin_arccos, hs]
  · have hneg : a.2 < 0 := lt_of_not_ge hy
    have hs : Real.sqrt (1-a.1^2) = -a.2 := by
      rw [he, Real.sqrt_sq_eq_abs, abs_of_neg hneg]
    apply Prod.ext
    · simpa [signedAngle, hy, Real.cos_neg] using
        (Real.cos_arccos hbounds.1 hbounds.2).symm
    · simp [signedAngle, hy, Real.sin_neg, Real.sin_arccos, hs]
def rotateAxis (θ : ℝ) (a : Point) : Point :=
  (Real.cos θ*a.1-Real.sin θ*a.2, Real.sin θ*a.1+Real.cos θ*a.2)

theorem rotateAxis_trig_diff (α β : ℝ) :
    rotateAxis (β-α) (Real.cos α, Real.sin α) =
      (Real.cos β, Real.sin β) := by
  apply Prod.ext
  · change Real.cos (β-α)*Real.cos α-Real.sin (β-α)*Real.sin α = Real.cos β
    rw [← Real.cos_add]
    congr 1
    ring
  · change Real.sin (β-α)*Real.cos α+Real.cos (β-α)*Real.sin α = Real.sin β
    rw [← Real.sin_add]
    congr 1
    ring

theorem rotate_right_axis (a b : Point)
    (ha : normSq a = 1) (hb : normSq b = 1)
    (hax : 0 ≤ a.1) (hbx : 0 ≤ b.1) :
    rotateAxis (signedAngle b-signedAngle a) a = b := by
  have hea := right_axis_trig a ha hax
  have heb := right_axis_trig b hb hbx
  calc
    rotateAxis (signedAngle b-signedAngle a) a =
        rotateAxis (signedAngle b-signedAngle a)
          (Real.cos (signedAngle a), Real.sin (signedAngle a)) :=
      congrArg (rotateAxis (signedAngle b-signedAngle a)) hea
    _ = (Real.cos (signedAngle b), Real.sin (signedAngle b)) :=
      rotateAxis_trig_diff (signedAngle a) (signedAngle b)
    _ = b := heb.symm

theorem construction_axis_first_quadrant (i : Owner) :
    0 ≤ (constructionSquare i).axis.1 ∧
    0 ≤ (constructionSquare i).axis.2 := by
  by_cases hi : 6 ≤ i.val
  · simp [constructionSquare, constructionAxis, hi,
      construction_cos_pos.le, construction_sin_pos.le]
  · simp [constructionSquare, constructionAxis, hi]

/-- Choose the square's axis in the rightward angular chart. The choice near
the positive vertical axis is rotated three quarter-turns, yielding a small
negative angle near the positive horizontal axis. -/
theorem exists_shallow_axis (q : UnitSquare) :
    ∃ r : UnitSquare, SameSquare q r ∧
      0 ≤ r.axis.1 ∧ |r.axis.2| ≤ r.axis.1 := by
  obtain ⟨r, hs, hx, hy⟩ := exists_firstQuadrant q
  by_cases h : r.axis.2 ≤ r.axis.1
  · exact ⟨r, hs, hx, by simpa [abs_of_nonneg hy] using h⟩
  · let rr := quarterTurn (quarterTurn (quarterTurn r))
    have hrr : SameSquare r rr :=
      (quarterTurn_sameSquare r).trans
        ((quarterTurn_sameSquare (quarterTurn r)).trans
          (quarterTurn_sameSquare (quarterTurn (quarterTurn r))))
    refine ⟨rr, hs.trans hrr, ?_, ?_⟩
    · simpa [rr, quarterTurn, perp] using hy
    · simpa [rr, quarterTurn, perp, abs_of_nonneg hx] using
        (le_of_lt (lt_of_not_ge h))

/-- Select the representative dictated by a source half-angle row. A row
near the chart endpoint `t = 1` is turned three times; a row near `t = 0`
keeps its original axis. Both represent the identical physical square. -/
def chartShallowSquare (q : UnitSquare) (nearOne : Bool) : UnitSquare :=
  if nearOne then quarterTurn (quarterTurn (quarterTurn q)) else q

theorem chartShallowSquare_same (q : UnitSquare) (nearOne : Bool) :
    SameSquare q (chartShallowSquare q nearOne) := by
  cases nearOne
  · exact SameSquare.refl q
  · exact (quarterTurn_sameSquare q).trans
      ((quarterTurn_sameSquare (quarterTurn q)).trans
        (quarterTurn_sameSquare (quarterTurn (quarterTurn q))))

@[simp] theorem chartShallowSquare_center (q : UnitSquare) (nearOne : Bool) :
    (chartShallowSquare q nearOne).center = q.center :=
  (chartShallowSquare_same q nearOne).center_eq.symm

theorem chartShallowSquare_axis_zero (q : UnitSquare) (t : ℝ)
    (haxis : q.axis = chartAxis t) :
    (chartShallowSquare q false).axis =
      ((1-t^2)/(1+t^2), 2*t/(1+t^2)) := by
  simpa [chartShallowSquare, chartAxis] using haxis

theorem chartShallowSquare_axis_one (q : UnitSquare) (t : ℝ)
    (haxis : q.axis = chartAxis t) :
    (chartShallowSquare q true).axis =
      (2*t/(1+t^2), -(1-t^2)/(1+t^2)) := by
  simp [chartShallowSquare, quarterTurn, perp, haxis, chartAxis]
  ring

/-- The three-quarter-turn chart parameter is exactly `(t-1)/(t+1)`.
This identity avoids choosing a branch of an inverse trigonometric function. -/
theorem chartAxis_shift_one (t : ℝ) (ht : 0 ≤ t) :
    chartAxis ((t-1)/(t+1)) =
      (2*t/(1+t^2), -(1-t^2)/(1+t^2)) := by
  have hp : t+1 ≠ 0 := ne_of_gt (by linarith : 0 < t+1)
  have hd : 1+t^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1+t^2)
  apply Prod.ext <;> dsimp [chartAxis] <;>
    field_simp [hp, hd] <;> ring

theorem chartShallowSquare_axis_one_chart (q : UnitSquare) (t : ℝ)
    (haxis : q.axis = chartAxis t) (ht : 0 ≤ t) :
    (chartShallowSquare q true).axis = chartAxis ((t-1)/(t+1)) := by
  rw [chartShallowSquare_axis_one q t haxis, chartAxis_shift_one t ht]

theorem chartShallowSquare_axis_x_nonneg (q : UnitSquare) (t : ℝ)
    (haxis : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (nearOne : Bool) : 0 ≤ (chartShallowSquare q nearOne).axis.1 := by
  have hd : 0 < 1+t^2 := by positivity
  cases nearOne
  · rw [chartShallowSquare_axis_zero q t haxis]
    exact div_nonneg (by nlinarith) hd.le
  · rw [chartShallowSquare_axis_one q t haxis]
    exact div_nonneg (by linarith) hd.le

/-- The chart representative after the physical cap-to-local quarter-turn.
Near `t = 0` a further square-axis quarter turn restores the source chart
axis. Near `t = 1` the transported axis already lies close to the positive
horizontal direction. -/
def quarterChartSquare (U V : ℝ) (q : UnitSquare) (nearOne : Bool) : UnitSquare :=
  if nearOne then quarterSquare U V q else quarterTurn (quarterSquare U V q)

theorem quarterChartSquare_same (U V : ℝ) (q : UnitSquare) (nearOne : Bool) :
    SameSquare (quarterSquare U V q) (quarterChartSquare U V q nearOne) := by
  cases nearOne
  · exact quarterTurn_sameSquare (quarterSquare U V q)
  · exact SameSquare.refl _

@[simp] theorem quarterChartSquare_center (U V : ℝ) (q : UnitSquare)
    (nearOne : Bool) :
    (quarterChartSquare U V q nearOne).center = quarterTo U V q.center := by
  cases nearOne <;> rfl

theorem quarterChartSquare_axis_low (U V : ℝ) (q : UnitSquare) (t : ℝ)
    (haxis : q.axis = chartAxis t) :
    (quarterChartSquare U V q false).axis = chartAxis t := by
  simpa [quarterChartSquare, quarterSquare, quarterTurn, perp] using haxis

theorem quarterChartSquare_axis_high (U V : ℝ) (q : UnitSquare) (t : ℝ)
    (haxis : q.axis = chartAxis t) (ht : 0 ≤ t) :
    (quarterChartSquare U V q true).axis = chartAxis ((t-1)/(t+1)) := by
  have hs := chartAxis_shift_one t ht
  rw [hs]
  simp [quarterChartSquare, quarterSquare, haxis, chartAxis]
  ring

theorem quarterChartSquare_axis_x_nonneg (U V : ℝ) (q : UnitSquare) (t : ℝ)
    (haxis : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (nearOne : Bool) : 0 ≤ (quarterChartSquare U V q nearOne).axis.1 := by
  have hd : 0 < 1+t^2 := by positivity
  cases nearOne
  · rw [quarterChartSquare_axis_low U V q t haxis]
    dsimp [chartAxis]
    exact div_nonneg (by nlinarith) hd.le
  · rw [quarterChartSquare_axis_high U V q t haxis ht0,
      chartAxis_shift_one t ht0]
    exact div_nonneg (by linarith) hd.le

/-- A complete physical pose is encoded by three coordinates per owner.
The angle difference is taken between normalized rightward axes. -/
def poseDisplacement (q : Owner → UnitSquare) (k : Fin 33) : ℝ :=
  let i : Owner := ⟨k.val / 3, by omega⟩
  if k.val % 3 = 0 then (q i).center.1-(constructionSquare i).center.1
  else if k.val % 3 = 1 then (q i).center.2-(constructionSquare i).center.2
  else signedAngle (q i).axis-signedAngle (constructionSquare i).axis

private theorem pose_index (i : Owner) (k : Fin 3) :
    (⟨(coordinate i k).val / 3, by omega⟩ : Owner) = i := by
  apply Fin.ext
  dsimp [coordinate]
  omega

theorem poseDisplacement_center_x (q : Owner → UnitSquare) (i : Owner) :
    poseDisplacement q (coordinate i 0) =
      (q i).center.1-(constructionSquare i).center.1 := by
  simp [poseDisplacement, pose_index, coordinate]

theorem poseDisplacement_center_y (q : Owner → UnitSquare) (i : Owner) :
    poseDisplacement q (coordinate i 1) =
      (q i).center.2-(constructionSquare i).center.2 := by
  unfold poseDisplacement
  have hidx := pose_index i (1 : Fin 3)
  have hm : (coordinate i 1).val % 3 = 1 := by dsimp [coordinate]; omega
  simp [hidx, hm]

theorem poseDisplacement_angle (q : Owner → UnitSquare) (i : Owner) :
    poseDisplacement q (coordinate i 2) =
      signedAngle (q i).axis-signedAngle (constructionSquare i).axis := by
  unfold poseDisplacement
  have hidx := pose_index i (2 : Fin 3)
  have hm : (coordinate i 2).val % 3 = 2 := by dsimp [coordinate]; omega
  simp [hidx, hm]

/-- Every rightward physical pose has an exact local-packet representation.
No small-angle or rectangle claim is used here. -/
theorem poseDisplacement_represents (q : Owner → UnitSquare)
    (hq : ∀ i, 0 ≤ (q i).axis.1) :
    ∀ i,
      (q i).center = perturbedCenter constructionSquare (poseDisplacement q) i ∧
      (q i).axis = perturbedAxis constructionSquare (poseDisplacement q) i := by
  intro i
  constructor
  · apply Prod.ext
    · change (q i).center.1 = (constructionSquare i).center.1 +
        poseDisplacement q (coordinate i 0)
      rw [poseDisplacement_center_x]
      ring
    · change (q i).center.2 = (constructionSquare i).center.2 +
        poseDisplacement q (coordinate i 1)
      rw [poseDisplacement_center_y]
      ring
  · have hbase := (construction_axis_first_quadrant i).1
    have hrot := rotate_right_axis (constructionSquare i).axis (q i).axis
      (constructionSquare i).axis_unit (q i).axis_unit
      hbase (hq i)
    change (q i).axis = rotateAxis
      (poseDisplacement q (coordinate i 2)) (constructionSquare i).axis
    rw [poseDisplacement_angle]
    exact hrot.symm

/-- Encode centers and an explicitly chosen radian displacement. In the near
capture proof the angular coordinate is `nearAngleDisplacement i t`, whose
closed-interval bound is checked separately. -/
def poseDisplacementWithAngles (q : Owner → UnitSquare)
    (θ : Owner → ℝ) (k : Fin 33) : ℝ :=
  let i : Owner := ⟨k.val / 3, by omega⟩
  if k.val % 3 = 0 then (q i).center.1-(constructionSquare i).center.1
  else if k.val % 3 = 1 then (q i).center.2-(constructionSquare i).center.2
  else θ i

theorem poseWithAngles_center_x (q : Owner → UnitSquare) (θ : Owner → ℝ)
    (i : Owner) : poseDisplacementWithAngles q θ (coordinate i 0) =
      (q i).center.1-(constructionSquare i).center.1 := by
  simp [poseDisplacementWithAngles, pose_index, coordinate]

theorem poseWithAngles_center_y (q : Owner → UnitSquare) (θ : Owner → ℝ)
    (i : Owner) : poseDisplacementWithAngles q θ (coordinate i 1) =
      (q i).center.2-(constructionSquare i).center.2 := by
  unfold poseDisplacementWithAngles
  have hidx := pose_index i (1 : Fin 3)
  have hm : (coordinate i 1).val % 3 = 1 := by dsimp [coordinate]; omega
  simp [hidx, hm]

theorem poseWithAngles_angle (q : Owner → UnitSquare) (θ : Owner → ℝ)
    (i : Owner) : poseDisplacementWithAngles q θ (coordinate i 2) = θ i := by
  unfold poseDisplacementWithAngles
  have hidx := pose_index i (2 : Fin 3)
  have hm : (coordinate i 2).val % 3 = 2 := by dsimp [coordinate]; omega
  simp [hidx, hm]

theorem poseWithAngles_represents (q : Owner → UnitSquare) (θ : Owner → ℝ)
    (hrot : ∀ i, (q i).axis = rotateAxis (θ i) (constructionSquare i).axis) :
    ∀ i,
      (q i).center = perturbedCenter constructionSquare
        (poseDisplacementWithAngles q θ) i ∧
      (q i).axis = perturbedAxis constructionSquare
        (poseDisplacementWithAngles q θ) i := by
  intro i
  constructor
  · apply Prod.ext
    · change (q i).center.1 = (constructionSquare i).center.1 +
        poseDisplacementWithAngles q θ (coordinate i 0)
      rw [poseWithAngles_center_x]
      ring
    · change (q i).center.2 = (constructionSquare i).center.2 +
        poseDisplacementWithAngles q θ (coordinate i 1)
      rw [poseWithAngles_center_y]
      ring
  · change (q i).axis = rotateAxis
      (poseDisplacementWithAngles q θ (coordinate i 2)) (constructionSquare i).axis
    rw [poseWithAngles_angle]
    exact hrot i

/-- Replace each orientation by an equivalent shallow-angle representative,
while preserving every physical square and the centered side bound. The
result is directly usable as a `LocalFeasible` pose at side `T`. -/
theorem centered_packing_has_local_pose {S : ℝ} (P : Packing 11 T)
    (hsmall : CenteredPacking P S) :
    ∃ (Q : Packing 11 T) (h : Displacement),
      CenteredPacking Q S ∧
      (∀ i, SameSquare (P.squares i) (Q.squares i)) ∧
      (∀ i,
        (Q.squares i).center = perturbedCenter constructionSquare h i ∧
        (Q.squares i).axis = perturbedAxis constructionSquare h i) := by
  classical
  choose r hs hx _hshallow using fun i => exists_shallow_axis (P.squares i)
  let Q := replaceSquares P r hs
  let h := poseDisplacement r
  refine ⟨Q, h, replaceSquares_centered P r hs hsmall, hs, ?_⟩
  exact poseDisplacement_represents r hx

end
end ElevenSquare.Tasks.T07
