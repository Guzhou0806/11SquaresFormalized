import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicFeatureRow
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCachedCover

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The geometric part of a moving feature row only needs a sound cover
at the current angle. This permits a cover checked through shared sign
certificates. -/
theorem symbolic_feature_row_choice_of_cover {n : ℕ}
    (P : Packing 11 coverCap) (i : Owner) (cell : Fin 16)
    (family : Fin n → Finset QPoint) (threshold : Fin n → ℕ)
    (t : ℝ) (l u : ℚ) (cert : SymbolicFeatureRowCertificate n)
    (hsource : cert.source = symbolicWallScaledSlab cell)
    (hcover : ∀ s : ℝ, (l : ℝ) ≤ s → s ≤ (u : ℝ) →
      ∀ x : Point, SymbolicPolygonContains cert.source s x →
        ∃ polygon ∈ cert.targets.map SymbolicFeatureTarget.polygon,
          SymbolicPolygonContains polygon s x)
    (htargetCheck : ∀ target ∈ cert.targets, target.Check)
    (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (ha : (P.squares i).axis = chartAxis t)
    (hcell : ClosedCell cell (normalizeCenter (P.squares i).center))
    (hmajority : ∀ feature polygon,
      SymbolicFeatureTarget.majority feature polygon ∈ cert.targets →
      SymbolicPolygonContains polygon t (P.squares i).center →
      BaselineMajorityCapture (family feature) (threshold feature) (P.squares i))
    (howned : ∀ p ∈ cert.blockerPoints, ∃ j : Owner,
      i ≠ j ∧ OpenSquare (P.squares j) (realPoint p)) :
    ∃ feature : Fin n,
      BaselineMajorityCapture (family feature) (threshold feature)
        (P.squares i) := by
  have hs : SymbolicPolygonContains cert.source t
      (P.squares i).center := by
    rw [hsource]
    exact symbolic_wall_scaled_slab_contains (P.squares i) cell t ha
      (P.contained i) hcell
  obtain ⟨polygon, hmem, hcenter⟩ :=
    hcover t hlt htu (P.squares i).center hs
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hmem
  cases target with
  | majority feature polygon =>
      exact ⟨feature, hmajority feature polygon htarget hcenter⟩
  | blocker polygon p h =>
      have hblock := htargetCheck _ htarget
      have hp : p ∈ cert.blockerPoints := by
        unfold SymbolicFeatureRowCertificate.blockerPoints
        exact (List.mem_filterMap SymbolicFeatureTarget.blockerPoint cert.targets).mpr
          ⟨.blocker polygon p h, htarget, rfl⟩
      obtain ⟨j, hij, hj⟩ := howned p hp
      exact False.elim (symbolic_point_block_impossible P i j hij p h
        polygon t ha ⟨hblock.1, hblock.2.1⟩ hblock.2.2 hcenter hj)

/-- A cached sign proof validates the original raw BSP and its original
Farkas witnesses, and then the moving feature row follows. -/
theorem symbolic_cached_feature_row_choice {n : ℕ}
    (P : Packing 11 coverCap) (i : Owner) (cell : Fin 16)
    (family : Fin n → Finset QPoint) (threshold : Fin n → ℕ)
    (t : ℝ) (l u : ℚ) (cert : SymbolicFeatureRowCertificate n)
    (cache : List CachedQuarticSign) (signs : SymbolicCoverSignRefs)
    (hsource : cert.source = symbolicWallScaledSlab cell)
    (hcache : SymbolicSignCache.Check cache)
    (hcover : SymbolicCoverSignRefs.Check cache cert.source
      (cert.targets.map SymbolicFeatureTarget.polygon) l u cert.cover signs)
    (htargetCheck : ∀ target ∈ cert.targets, target.Check)
    (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (ha : (P.squares i).axis = chartAxis t)
    (hcell : ClosedCell cell (normalizeCenter (P.squares i).center))
    (hmajority : ∀ feature polygon,
      SymbolicFeatureTarget.majority feature polygon ∈ cert.targets →
      SymbolicPolygonContains polygon t (P.squares i).center →
      BaselineMajorityCapture (family feature) (threshold feature) (P.squares i))
    (howned : ∀ p ∈ cert.blockerPoints, ∃ j : Owner,
      i ≠ j ∧ OpenSquare (P.squares j) (realPoint p)) :
    ∃ feature : Fin n,
      BaselineMajorityCapture (family feature) (threshold feature)
        (P.squares i) := by
  exact symbolic_feature_row_choice_of_cover P i cell family threshold t l u
    cert hsource
    (fun s hsl hsu x hx =>
      symbolic_cached_cover_sound cache hcache cert.source
        (cert.targets.map SymbolicFeatureTarget.polygon) l u cert.cover
        signs hcover s hsl hsu x hx)
    htargetCheck hlt htu ha hcell hmajority howned

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_cached_feature_row_choice
