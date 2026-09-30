import ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window019.Data

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window019
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem source_matches : baselineSlab 1 margin = source := by
  change baselineSlab ⟨1, by decide⟩ margin = source
  norm_num [baselineSlab, baselineCellPolygon, baselineCenterBox, baselineBisector,
    baselineRationalSite, baselineRationalCap, margin, source, List.finRange]

theorem wall_checked : BaselineWallCheck (51/64) (13/16) margin := by
  norm_num [BaselineWallCheck, margin]

theorem row_contains (q : UnitSquare)
    (hcell : ClosedCell 1 (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : q.axis = chartAxis t)
    (hl : ((51/64) : ℝ) ≤ t) (hu : t ≤ ((13/16) : ℝ)) : inputRow.contains q := by
  refine ⟨?_, t, ht0, ht1, ?_, ?_, ha⟩
  · change q.center ∈ source.carrier
    rw [← source_matches]
    exact baseline_slab_contains q 1 (51/64) (13/16) margin t wall_checked (by norm_num at hl ⊢; exact hl) (by norm_num at hu ⊢; exact hu) ha hcont
      (baselineCellPolygon_contains hcell)
  · simpa [inputRow] using hl
  · simpa [inputRow] using hu

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G004.FixedCell01Window019
