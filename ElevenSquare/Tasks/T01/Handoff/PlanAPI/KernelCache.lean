import ElevenSquare.Tasks.T01.Handoff.PlanAPI.Universal

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01
noncomputable section

/-- The geometry shared by all universal collision checks with the same pair
of strict cores and angle intervals. It can be proved once and reused for
different target regions and different partner center domains. -/
structure UniversalKernelCertificate where
  currentCore : List QPoint
  partnerCore : List QPoint
  differenceVertices : List QPoint
  differenceCorners : List (ℕ × ℕ)
  difference : Polygon
  witnesses : List DifferenceWitness

def UniversalKernelCertificate.Check (k : UniversalKernelCertificate)
    (currentRow partnerRow : PoseRow) : Prop :=
  (∀ v ∈ k.currentCore,
    BaselineCoreVertexCheck v currentRow.lo currentRow.hi) ∧
  (∀ v ∈ k.partnerCore,
    BaselineCoreVertexCheck v partnerRow.lo partnerRow.hi) ∧
  PolygonCornerCheck k.differenceVertices k.difference k.differenceCorners ∧
  DifferenceVerticesCheck k.partnerCore k.currentCore
    k.differenceVertices k.witnesses

instance universalKernelCheckDecidable (k : UniversalKernelCertificate)
    (currentRow partnerRow : PoseRow) : Decidable (k.Check currentRow partnerRow) := by
  unfold UniversalKernelCertificate.Check
  infer_instance

/-- A kernel proof depends on the angle intervals, not on either center
polygon. It can therefore be shared by partners with the same strict cores
and angle bins even when their center domains differ. -/
theorem UniversalKernelCertificate.check_same_intervals
    (k : UniversalKernelCertificate)
    (currentRow currentRow' partnerRow partnerRow' : PoseRow)
    (hk : k.Check currentRow partnerRow)
    (hcl : currentRow.lo = currentRow'.lo)
    (hch : currentRow.hi = currentRow'.hi)
    (hpl : partnerRow.lo = partnerRow'.lo)
    (hph : partnerRow.hi = partnerRow'.hi) :
    k.Check currentRow' partnerRow' := by
  refine ⟨?_, ?_, hk.2.2.1, hk.2.2.2⟩
  · intro v hv
    simpa only [← hcl, ← hch] using hk.1 v hv
  · intro v hv
    simpa only [← hpl, ← hph] using hk.2.1 v hv

/-- Only the domain corners and a facet support split vary with a particular
region/partner-row pair. The kernel's vertices and strict core checks are not
repeated in this predicate. -/
structure CachedRegionCertificate where
  domainVertices : List QPoint
  domainCorners : List (ℕ × ℕ)
  facetBounds : List ℚ

def CachedRegionCertificate.Check (c : CachedRegionCertificate)
    (k : UniversalKernelCertificate) (regionVertices : List QPoint)
    (partnerRow : PoseRow) : Prop :=
  PolygonCornerCheck c.domainVertices partnerRow.centers c.domainCorners ∧
  FacetSupportCheck regionVertices c.domainVertices k.difference c.facetBounds

instance cachedRegionCheckDecidable (c : CachedRegionCertificate)
    (k : UniversalKernelCertificate) (regionVertices : List QPoint)
    (partnerRow : PoseRow) : Decidable (c.Check k regionVertices partnerRow) := by
  unfold CachedRegionCertificate.Check
  infer_instance

theorem cached_region_collision (k : UniversalKernelCertificate)
    (c : CachedRegionCertificate) (regionVertices : List QPoint)
    (region : Polygon) (regionCorners : List (ℕ × ℕ))
    (currentRow partnerRow : PoseRow)
    (hk : k.Check currentRow partnerRow)
    (hc : c.Check k regionVertices partnerRow)
    (hregion : PolygonCornerCheck regionVertices region regionCorners)
    (q r : UnitSquare) (hq : currentRow.contains q)
    (hr : partnerRow.contains r)
    (hcenter : q.center ∈ region.carrier) :
    ∃ point, OpenSquare q point ∧ OpenSquare r point := by
  let cert : UniversalSupportRowCertificate :=
    { domainVertices := c.domainVertices
      domainCorners := c.domainCorners
      partnerCore := k.partnerCore
      differenceVertices := k.differenceVertices
      differenceCorners := k.differenceCorners
      difference := k.difference
      witnesses := k.witnesses
      facetBounds := c.facetBounds }
  have hcert : cert.Check k.currentCore regionVertices partnerRow := by
    exact ⟨hc.1, hk.2.1, hk.2.2.1, hk.2.2.2, hc.2⟩
  have hcore : CoreFits (rationalHull k.currentCore) q :=
    baseline_row_core_checked currentRow k.currentCore hk.1 q hq
  exact universal_support_row_collision cert k.currentCore regionVertices region
    partnerRow hcert (polygon_corner_check_sound _ _ _ hregion)
    q r hr hcore hcenter

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.cached_region_collision
