import ElevenSquare.Tasks.T07.CaptureRoleDiamond
import ElevenSquare.Tasks.T07.NearStateBridge

/-! The first role remains at its full angular interval after the three
conservative branch guards. The checked near packet has a strict gap around
half-angle `1/2` for that role. Subsequent capture pruning must narrow this
row before native near-state inclusion can hold. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem roleDiamondNear_row0_unchanged :
    roleDiamondNearState.rows (0 : Owner) =
      roleDiamondSeed.rows (0 : Owner) := by
  rfl

theorem roleDiamondNear_row0_full :
    ∃ r ∈ roleDiamondNearState.rows (0 : Owner),
      r.lo = 0 ∧ r.hi = 1 := by
  let row : PoseRow :=
    { lo := 0, hi := 1, centers := seedCellPolygon (roleCell (0 : Owner)) }
  refine ⟨row, ?_, by rfl, by rfl⟩
  rw [roleDiamondNear_row0_unchanged]
  rw [(roleDiamondSeed_cell (0 : Owner)).1]
  simp

theorem nearOuter_row0_excludes_mid_angle :
    ∀ r ∈ nearOuterState.rows (0 : Owner),
      ¬ ((r.lo : ℝ) ≤ 1/2 ∧ 1/2 ≤ (r.hi : ℝ)) := by
  intro r hr ⟨hlo, hhi⟩
  obtain ⟨nr, hnr, rfl⟩ := List.mem_map.mp hr
  have hmem : nr ∈ nearRows0 := by simpa only [nearRows] using hnr
  have hv := (List.forall_iff_forall_mem.mp (nearRows0_valid)) nr hmem
  have he := (List.forall_iff_forall_mem.mp nearRows0_angle_extrema) nr hmem
  have hbranch : nr.hi ≤ Rat.divInt 1 2 ∨ Rat.divInt 1 2 ≤ nr.lo := by
    simpa only [NearPoseRow.Valid, nearAxis, reduceIte] using hv.2.2.2.1
  change (nr.lo : ℝ) ≤ 1/2 at hlo
  change 1/2 ≤ (nr.hi : ℝ) at hhi
  rcases hbranch with hlow | hhigh
  · have hh : (nr.hi : ℝ) ≤ (Rat.divInt 9 7936 : ℝ) := by
      exact_mod_cast he.1 hlow
    have hg : (Rat.divInt 9 7936 : ℝ) < 1/2 := by norm_num [Rat.divInt]
    exact (not_le_of_gt (lt_of_le_of_lt hh hg)) hhi
  · have hl : (Rat.divInt 496 497 : ℝ) ≤ (nr.lo : ℝ) := by
      exact_mod_cast he.2 hhigh
    have hg : 1/2 < (Rat.divInt 496 497 : ℝ) := by norm_num [Rat.divInt]
    exact (not_le_of_gt (lt_of_lt_of_le hg hl)) hlo

def midAngleCellSquare : UnitSquare where
  center := realPoint (physicalSite (roleCell (0 : Owner)))
  axis := chartAxis (1/2)
  axis_unit := by norm_num [chartAxis, normSq, dot]

theorem midAngleCellSquare_in_diamond_near :
    RowsContain (roleDiamondNearState.rows (0 : Owner)) midAngleCellSquare := by
  have hsite : ClosedCell (roleCell (0 : Owner))
      (coverSite (roleCell (0 : Owner))) := by
    constructor
    · norm_num [InUnitBox, roleCell, coverSite]
    · intro j
      have hz : coordinateDistanceSq (coverSite (roleCell (0 : Owner)))
          (coverSite (roleCell (0 : Owner))) = 0 := by
        simp [coordinateDistanceSq]
      rw [hz]
      dsimp [coordinateDistanceSq]
      positivity
  let row : PoseRow :=
    { lo := 0, hi := 1, centers := seedCellPolygon (roleCell (0 : Owner)) }
  have hrow : row ∈ roleDiamondNearState.rows (0 : Owner) := by
    rw [roleDiamondNear_row0_unchanged]
    rw [(roleDiamondSeed_cell (0 : Owner)).1]
    simp [row]
  refine ⟨row, hrow, ?_⟩
  have hcenter : midAngleCellSquare.center ∈ row.centers.carrier := by
    apply seedCellPolygon_sound
    change ClosedCell (roleCell (0 : Owner))
      (normalizeCenter (realPoint (physicalSite (roleCell (0 : Owner)))))
    rw [normalized_physicalSite]
    exact hsite
  exact ⟨hcenter, 1/2, by norm_num, by norm_num,
    by norm_num [row], by norm_num [row], rfl⟩

/-- The conservative three-guard near state still contains a role-zero square
at half-angle `1/2`, while every checked final near row excludes that angle.
It therefore cannot be handed directly to the final near packet. -/
theorem roleDiamondNear_not_subsumed :
    ¬ NearRowsSubsumed roleDiamondNearState := by
  intro hsub
  obtain ⟨r, hr, _, t, ht0, ht1, htlo, hthi, haxis⟩ :=
    hsub (0 : Owner) midAngleCellSquare midAngleCellSquare_in_diamond_near
  have ht : t = 1/2 :=
    chartAxis_parameter_unique (q := midAngleCellSquare) (t₀ := 1/2)
      (by norm_num) (by rfl) t ht0 ht1 haxis
  exact nearOuter_row0_excludes_mid_angle r hr
    ⟨by simpa only [ht] using htlo, by simpa only [ht] using hthi⟩

end
end ElevenSquare.Tasks.T07
