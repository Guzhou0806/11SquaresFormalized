import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicFieldRow

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A symbolic field row may certify any finite majority threshold. The
point-blocker branch uses the same strict ownership contradiction for every
threshold. -/
theorem symbolic_majority_field_row (P : Packing 11 coverCap)
    (i : Owner) (cell : Fin 16) (sites : Finset QPoint) (k : ℕ)
    (t : ℝ) (l u : ℚ) (cert : SymbolicFieldRowCertificate)
    (hc : cert.Check cell l u)
    (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
    (ha : (P.squares i).axis = chartAxis t)
    (hcell : ClosedCell cell (normalizeCenter (P.squares i).center))
    (hmedian : ∀ polygon,
      SymbolicFieldTarget.median polygon ∈ cert.targets →
      SymbolicPolygonContains polygon t (P.squares i).center →
      BaselineMajorityCapture sites k (P.squares i))
    (howned : ∀ p ∈ cert.blockerPoints, ∃ j : Owner,
      i ≠ j ∧ OpenSquare (P.squares j) (realPoint p)) :
    BaselineMajorityCapture sites k (P.squares i) := by
  have hsource : SymbolicPolygonContains cert.source t
      (P.squares i).center := by
    rw [hc.1]
    exact symbolic_wall_scaled_slab_contains (P.squares i) cell t ha
      (P.contained i) hcell
  obtain ⟨polygon, hmem, hcenter⟩ := symbolic_cover_sound
    cert.source (cert.targets.map SymbolicFieldTarget.polygon) l u
    cert.cover hc.2.1 t hlt htu (P.squares i).center hsource
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hmem
  cases target with
  | median polygon => exact hmedian polygon htarget hcenter
  | blocker polygon p h =>
      have hblock := hc.2.2 _ htarget
      have hp : p ∈ cert.blockerPoints := by
        unfold SymbolicFieldRowCertificate.blockerPoints
        exact (List.mem_filterMap SymbolicFieldTarget.blockerPoint cert.targets).mpr
          ⟨.blocker polygon p h, htarget, rfl⟩
      obtain ⟨j, hij, hj⟩ := howned p hp
      exact False.elim (symbolic_point_block_impossible P i j hij p h
        polygon t ha ⟨hblock.1, hblock.2.1⟩ hblock.2.2 hcenter hj)

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_majority_field_row
