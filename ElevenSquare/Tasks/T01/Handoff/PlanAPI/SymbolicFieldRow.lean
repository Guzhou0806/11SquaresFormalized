import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicPointTarget
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicIntervalCover
import ElevenSquare.Tasks.T01.Majority

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Exact target classification for a symbolic field row. The median branch
is discharged by a separate finite support certificate; blocker branches
carry four checked strict point-capture facets. -/
inductive SymbolicFieldTarget where
  | median (polygon : List SymbolicFacet)
  | blocker (polygon : List SymbolicFacet) (point : QPoint) (halfWidth : ℚ)
  deriving DecidableEq

def SymbolicFieldTarget.polygon : SymbolicFieldTarget → List SymbolicFacet
  | .median polygon => polygon
  | .blocker polygon _ _ => polygon

def SymbolicFieldTarget.blockerPoint : SymbolicFieldTarget → Option QPoint
  | .median _ => none
  | .blocker _ p _ => some p

def SymbolicFieldTarget.Check : SymbolicFieldTarget → Prop
  | .median _ => True
  | .blocker polygon p h =>
      0 ≤ h ∧ h < 1/2 ∧
        ∀ f ∈ symbolicPointTarget p h, f ∈ polygon

instance symbolicFieldTargetCheckDecidable (target : SymbolicFieldTarget) :
    Decidable target.Check := by
  cases target <;> dsimp [SymbolicFieldTarget.Check] <;> infer_instance

/-- A raw moving-BSP row certificate with finite target classifications.
The source identity ties its 24 facets to the actual container and cell. -/
structure SymbolicFieldRowCertificate where
  source : List SymbolicFacet
  targets : List SymbolicFieldTarget
  cover : SymbolicCoverCertificate

def SymbolicFieldRowCertificate.blockerPoints
    (cert : SymbolicFieldRowCertificate) : List QPoint :=
  cert.targets.filterMap SymbolicFieldTarget.blockerPoint

def SymbolicFieldRowCertificate.Check (cert : SymbolicFieldRowCertificate)
    (cell : Fin 16) (l u : ℚ) : Prop :=
  cert.source = symbolicWallScaledSlab cell ∧
    cert.cover.Check cert.source (cert.targets.map SymbolicFieldTarget.polygon) l u ∧
    ∀ target ∈ cert.targets, target.Check

instance symbolicFieldRowCertificateCheckDecidable
    (cert : SymbolicFieldRowCertificate) (cell : Fin 16) (l u : ℚ) :
    Decidable (cert.Check cell l u) := by
  unfold SymbolicFieldRowCertificate.Check
  infer_instance

/-- Each actual center in the row reaches a median target or a point already
captured by another square. In the latter case strict interior disjointness
rules out the square, so the median majority capture is forced. -/
theorem symbolic_field_row_majority (P : Packing 11 coverCap)
    (i : Owner) (cell : Fin 16) (sites : Finset QPoint) (t : ℝ) (l u : ℚ)
    (cert : SymbolicFieldRowCertificate)
    (hc : cert.Check cell l u)
    (hlt : (l:ℝ) ≤ t) (htu : t ≤ (u:ℝ))
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
    rw [hc.1]
    exact symbolic_wall_scaled_slab_contains (P.squares i) cell t ha
      (P.contained i) hcell
  obtain ⟨polygon, hmem, hcenter⟩ := symbolic_cover_sound
    cert.source (cert.targets.map SymbolicFieldTarget.polygon) l u
    cert.cover hc.2.1 t hlt htu (P.squares i).center hsource
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hmem
  cases target with
  | median polygon =>
      exact hmedian polygon htarget hcenter
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

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_field_row_majority
