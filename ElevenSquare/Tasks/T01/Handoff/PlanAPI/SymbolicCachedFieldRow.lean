import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCachedCover
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicFieldRow

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Reusable polynomial signs certify the same raw geometric row and actual
square semantics. Target classification and strict blocker ownership stay explicit. -/
theorem symbolic_cached_field_row_majority (P : Packing 11 coverCap)
    (i : Owner) (cell : Fin 16) (sites : Finset QPoint) (t : ℝ) (l u : ℚ)
    (cert : SymbolicFieldRowCertificate)
    (cache : List CachedQuarticSign) (signs : SymbolicCoverSignRefs)
    (hcache : SymbolicSignCache.Check cache)
    (hsource_eq : cert.source = symbolicWallScaledSlab cell)
    (hcover : SymbolicCoverSignRefs.Check cache cert.source
      (cert.targets.map SymbolicFieldTarget.polygon) l u cert.cover signs)
    (htargets : ∀ target ∈ cert.targets, target.Check)
    (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (ha : (P.squares i).axis = chartAxis t)
    (hcell : ClosedCell cell (normalizeCenter (P.squares i).center))
    (hmedian : ∀ polygon,
      SymbolicFieldTarget.median polygon ∈ cert.targets →
      SymbolicPolygonContains polygon t (P.squares i).center →
      BaselineMajorityCapture sites 2 (P.squares i))
    (howned : ∀ p ∈ cert.blockerPoints, ∃ j : Owner,
      i ≠ j ∧ OpenSquare (P.squares j) (realPoint p)) :
    BaselineMajorityCapture sites 2 (P.squares i) := by
  have hsource : SymbolicPolygonContains cert.source t
      (P.squares i).center := by
    rw [hsource_eq]
    exact symbolic_wall_scaled_slab_contains (P.squares i) cell t ha
      (P.contained i) hcell
  obtain ⟨polygon, hmem, hcenter⟩ := symbolic_cached_cover_sound
    cache hcache cert.source (cert.targets.map SymbolicFieldTarget.polygon)
    l u cert.cover signs hcover t hlt htu (P.squares i).center hsource
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hmem
  cases target with
  | median polygon => exact hmedian polygon htarget hcenter
  | blocker polygon p h =>
      have hblock := htargets _ htarget
      have hp : p ∈ cert.blockerPoints := by
        unfold SymbolicFieldRowCertificate.blockerPoints
        exact (List.mem_filterMap SymbolicFieldTarget.blockerPoint cert.targets).mpr
          ⟨.blocker polygon p h, htarget, rfl⟩
      obtain ⟨j, hij, hj⟩ := howned p hp
      exact False.elim (symbolic_point_block_impossible P i j hij p h
        polygon t ha ⟨hblock.1, hblock.2.1⟩ hblock.2.2 hcenter hj)

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_cached_field_row_majority
