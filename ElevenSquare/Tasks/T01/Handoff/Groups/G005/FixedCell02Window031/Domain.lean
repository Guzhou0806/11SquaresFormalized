import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window031.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window031
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem source_matches : baselineSlab 2 margin = source := by
  change baselineSlab ⟨2, by decide⟩ margin = source
  norm_num [baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, margin, source, List.finRange]

theorem wall_checked : BaselineWallCheck (15/32) (1/2) margin := by
  norm_num [BaselineWallCheck, margin]

theorem row_contains (q : UnitSquare)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : q.axis = chartAxis t)
    (hl : ((15/32) : ℝ) ≤ t) (hu : t ≤ ((1/2) : ℝ)) : inputRow.contains q := by
  refine ⟨?_, t, ht0, ht1, ?_, ?_, ha⟩
  · change q.center ∈ source.carrier
    rw [← source_matches]
    exact baseline_slab_contains q 2 (15/32) (1/2) margin t wall_checked (by norm_num at hl ⊢; exact hl) (by norm_num at hu ⊢; exact hu) ha hcont
      (baselineCellPolygon_contains hcell)
  · simpa [inputRow] using hl
  · simpa [inputRow] using hu

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window031
