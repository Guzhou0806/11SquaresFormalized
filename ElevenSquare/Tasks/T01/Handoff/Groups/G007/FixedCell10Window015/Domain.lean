import ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window015.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window015
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem source_matches : baselineSlab 10 margin = source := by
  change baselineSlab ⟨10, by decide⟩ margin = source
  norm_num [baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, margin, source, List.finRange]

theorem wall_checked : BaselineWallCheck (27/32) (7/8) margin := by
  norm_num [BaselineWallCheck, margin]

theorem row_contains (q : UnitSquare)
    (hcell : ClosedCell 10 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : q.axis = chartAxis t)
    (hl : ((27/32) : ℝ) ≤ t) (hu : t ≤ ((7/8) : ℝ)) : inputRow.contains q := by
  refine ⟨?_, t, ht0, ht1, ?_, ?_, ha⟩
  · change q.center ∈ source.carrier
    rw [← source_matches]
    exact baseline_slab_contains q 10 (27/32) (7/8) margin t wall_checked (by norm_num at hl ⊢; exact hl) (by norm_num at hu ⊢; exact hu) ha hcont
      (baselineCellPolygon_contains hcell)
  · simpa [inputRow] using hl
  · simpa [inputRow] using hu

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007.FixedCell10Window015
