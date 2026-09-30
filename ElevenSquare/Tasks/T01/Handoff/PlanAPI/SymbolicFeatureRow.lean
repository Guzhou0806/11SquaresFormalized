import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicFieldRow

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A moving target certifies one chosen feature, or excludes the square
through a point strictly owned by a different square. -/
inductive SymbolicFeatureTarget (n : ℕ) where
  | majority (feature : Fin n) (polygon : List SymbolicFacet)
  | blocker (polygon : List SymbolicFacet) (point : QPoint) (halfWidth : ℚ)
  deriving DecidableEq

def SymbolicFeatureTarget.polygon {n : ℕ} :
    SymbolicFeatureTarget n → List SymbolicFacet
  | .majority _ polygon => polygon
  | .blocker polygon _ _ => polygon

def SymbolicFeatureTarget.blockerPoint {n : ℕ} :
    SymbolicFeatureTarget n → Option QPoint
  | .majority _ _ => none
  | .blocker _ p _ => some p

def SymbolicFeatureTarget.Check {n : ℕ} : SymbolicFeatureTarget n → Prop
  | .majority _ _ => True
  | .blocker polygon p h =>
      0 ≤ h ∧ h < 1/2 ∧
        ∀ f ∈ symbolicPointTarget p h, f ∈ polygon

instance symbolicFeatureTargetCheckDecidable {n : ℕ}
    (target : SymbolicFeatureTarget n) : Decidable target.Check := by
  cases target <;> dsimp [SymbolicFeatureTarget.Check] <;> infer_instance

structure SymbolicFeatureRowCertificate (n : ℕ) where
  source : List SymbolicFacet
  targets : List (SymbolicFeatureTarget n)
  cover : SymbolicCoverCertificate

def SymbolicFeatureRowCertificate.blockerPoints {n : ℕ}
    (cert : SymbolicFeatureRowCertificate n) : List QPoint :=
  cert.targets.filterMap SymbolicFeatureTarget.blockerPoint

def SymbolicFeatureRowCertificate.Check {n : ℕ}
    (cert : SymbolicFeatureRowCertificate n)
    (cell : Fin 16) (l u : ℚ) : Prop :=
  cert.source = symbolicWallScaledSlab cell ∧
    cert.cover.Check cert.source
      (cert.targets.map SymbolicFeatureTarget.polygon) l u ∧
    ∀ target ∈ cert.targets, target.Check

instance symbolicFeatureRowCertificateCheckDecidable {n : ℕ}
    (cert : SymbolicFeatureRowCertificate n)
    (cell : Fin 16) (l u : ℚ) : Decidable (cert.Check cell l u) := by
  unfold SymbolicFeatureRowCertificate.Check
  infer_instance

/-- A checked moving cover gives one feature capture when every point target
is strictly owned by another square. The feature may vary by cover branch. -/
theorem symbolic_feature_row_choice {n : ℕ}
    (P : Packing 11 coverCap) (i : Owner) (cell : Fin 16)
    (family : Fin n → Finset QPoint) (threshold : Fin n → ℕ)
    (t : ℝ) (l u : ℚ) (cert : SymbolicFeatureRowCertificate n)
    (hc : cert.Check cell l u)
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
  have hsource : SymbolicPolygonContains cert.source t
      (P.squares i).center := by
    rw [hc.1]
    exact symbolic_wall_scaled_slab_contains (P.squares i) cell t ha
      (P.contained i) hcell
  obtain ⟨polygon, hmem, hcenter⟩ := symbolic_cover_sound
    cert.source (cert.targets.map SymbolicFeatureTarget.polygon) l u
    cert.cover hc.2.1 t hlt htu (P.squares i).center hsource
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hmem
  cases target with
  | majority feature polygon =>
      exact ⟨feature, hmajority feature polygon htarget hcenter⟩
  | blocker polygon p h =>
      have hblock := hc.2.2 _ htarget
      have hp : p ∈ cert.blockerPoints := by
        unfold SymbolicFeatureRowCertificate.blockerPoints
        exact List.mem_filterMap.mpr
          ⟨.blocker polygon p h, htarget, rfl⟩
      obtain ⟨j, hij, hj⟩ := howned p hp
      exact False.elim (symbolic_point_block_impossible P i j hij p h
        polygon t ha ⟨hblock.1, hblock.2.1⟩ hblock.2.2 hcenter hj)

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_feature_row_choice
