import ElevenSquare.Tasks.T01.CornerOwnership

namespace ElevenSquare.Tasks.T01.CornerSeed005
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

def point : QPoint := ((498020679/500000000), (997648353/1000000000))

def witnessX : BaselineCombination := [(5, (360029000000/286195087637)), (9, (174831000000/286195087637))]

theorem bound_x_checked : BaselineImplicationCheck (baselineCellPolygon 0) ⟨1, 0, point.1+1/3⟩ witnessX := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro iw hi
    simp only [witnessX, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals norm_num [baselineCellPolygon, baselineCenterBox]
  all_goals norm_num [baselineCombinationSum, baselineZeroHalfplane, witnessX, point,
    baselineCellPolygon, baselineCenterBox, baselineBisector, baselineRationalSite,
    baselineRationalCap, List.finRange, List.getD]

def witnessY : BaselineCombination := [(1, (1267/178307)), (8, (1000000/534921))]

theorem bound_y_checked : BaselineImplicationCheck (baselineCellPolygon 0) ⟨0, 1, point.2+1/3⟩ witnessY := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro iw hi
    simp only [witnessY, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals norm_num [baselineCellPolygon, baselineCenterBox]
  all_goals norm_num [baselineCombinationSum, baselineZeroHalfplane, witnessY, point,
    baselineCellPolygon, baselineCenterBox, baselineBisector, baselineRationalSite,
    baselineRationalCap, List.finRange, List.getD]

/-- The actual archived corner seed, with no angle-subdivision premise. -/
theorem point_owned (q : UnitSquare)
    (hcell : ClosedCell 0 (normalizeCenter q.center))
    (hcont : ∀ z, ClosedSquare q z → InContainer coverCap z)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    OpenSquare q (realPoint point) := by
  have hx := baseline_implication_check_sound _ _ _ bound_x_checked q.center
    (baselineCellPolygon_contains hcell)
  have hy := baseline_implication_check_sound _ _ _ bound_y_checked q.center
    (baselineCellPolygon_contains hcell)
  dsimp [Halfplane.contains] at hx hy
  push_cast at hx hy
  obtain ⟨t, ht0, ht1, ha⟩ := hchart
  have hd : 0 < 1+t^2 := by positivity
  have ht2 : t^2 ≤ 1 := by nlinarith
  have hax : 0 ≤ q.axis.1 := by
    rw [ha]
    exact div_nonneg (sub_nonneg.mpr ht2) hd.le
  have hay : 0 ≤ q.axis.2 := by
    rw [ha]
    exact div_nonneg (by positivity) hd.le
  apply corner_point_owned q (realPoint point) hcont hax hay
  · norm_num [point, realPoint]
  · norm_num [point, realPoint]
  · simpa [realPoint] using hx
  · simpa [realPoint] using hy

end
end ElevenSquare.Tasks.T01.CornerSeed005
