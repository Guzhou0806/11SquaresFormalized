import ElevenSquare.Tasks.T07.LocalMinkowski
import ElevenSquare.Tasks.T07.LocalTraceCover
import ElevenSquare.Pending.S05_Trace

/-! A semantic interface from finite field-polygon certificates to a sound
terminal `VerifiedStep`. Its premises deliberately include the source pose
cover, genuinely owned physical hull, and strict physical core containment.
The finite triangle/vertex data alone do not establish these premises. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def RegionCollisionCertificate (s : PoseState) (i : Owner)
    (region : Polygon) : Prop :=
  ∃ (j : Owner) (K Q vertices : List QPoint),
    i ≠ j ∧
    region.carrier ⊆ rationalHull vertices ∧
    (∀ v ∈ vertices, v ∈ pairwiseQDiff K Q) ∧
    rationalHull (K.map qpointFieldNormalize) ⊆ rationalHull (s.owned j) ∧
    (∀ q, RowsContain (s.rows i) q →
      CoreFits (rationalHull (Q.map qpointFieldNormalize)) q)

theorem terminal_prune_of_field_polygon_cover
    (s : PoseState) (i : Owner) (domain : Polygon)
    (regions : List Polygon)
    (hsource : ∀ q, RowsContain (s.rows i) q →
      toField q.center ∈ domain.carrier)
    (hcover : PolygonCoverCert regions domain)
    (hregions : ∀ region ∈ regions, RegionCollisionCertificate s i region) :
    VerifiedStep s (replaceRows s i []) := by
  apply VerifiedStep.prunePosewise
  intro q hq
  right
  obtain ⟨region, hregion⟩ := Set.mem_iUnion.mp (hcover.sound (hsource q hq))
  obtain ⟨hmember, hc⟩ := Set.mem_iUnion.mp hregion
  obtain ⟨j, K, Q, vertices, hij, htriangle, hvertices, howned, hcore⟩ :=
    hregions region hmember
  refine ⟨j, hij, rationalHull (Q.map qpointFieldNormalize), hcore q hq, ?_⟩
  exact fieldPolygon_center_forbidden K Q region q.center
    (rationalHull (s.owned j))
    (rationalHull (Q.map qpointFieldNormalize))
    (htriangle.trans
      (rationalHull_vertices_subset_pairwiseQDiff K Q vertices hvertices))
    howned (Set.Subset.refl _) hc

/-- A terminal state may have many angular rows. The strict core is checked
only on the source row associated with its field polygon, so different rows
can use different rational core polygons. -/
def RowRegionCollisionCertificate (s : PoseState) (i : Owner)
    (r : PoseRow) (region : Polygon) : Prop :=
  ∃ (j : Owner) (K Q vertices : List QPoint),
    i ≠ j ∧
    region.carrier ⊆ rationalHull vertices ∧
    (∀ v ∈ vertices, v ∈ pairwiseQDiff K Q) ∧
    rationalHull (K.map qpointFieldNormalize) ⊆ rationalHull (s.owned j) ∧
    (∀ q, r.contains q →
      CoreFits (rationalHull (Q.map qpointFieldNormalize)) q)

theorem terminal_prune_of_rowwise_field_covers
    (s : PoseState) (i : Owner)
    (domain : PoseRow → Polygon)
    (regions : PoseRow → List Polygon)
    (hsource : ∀ r ∈ s.rows i, ∀ q, r.contains q →
      toField q.center ∈ (domain r).carrier)
    (hcover : ∀ r ∈ s.rows i, PolygonCoverCert (regions r) (domain r))
    (hregions : ∀ r ∈ s.rows i, ∀ region ∈ regions r,
      RowRegionCollisionCertificate s i r region) :
    VerifiedStep s (replaceRows s i []) := by
  apply VerifiedStep.prunePosewise
  intro q hq
  right
  obtain ⟨r, hr, hqr⟩ := hq
  obtain ⟨region, hregion⟩ :=
    Set.mem_iUnion.mp ((hcover r hr).sound (hsource r hr q hqr))
  obtain ⟨hmember, hc⟩ := Set.mem_iUnion.mp hregion
  obtain ⟨j, K, Q, vertices, hij, htriangle, hvertices, howned, hcore⟩ :=
    hregions r hr region hmember
  refine ⟨j, hij, rationalHull (Q.map qpointFieldNormalize), hcore q hqr, ?_⟩
  exact fieldPolygon_center_forbidden K Q region q.center
    (rationalHull (s.owned j))
    (rationalHull (Q.map qpointFieldNormalize))
    (htriangle.trans
      (rationalHull_vertices_subset_pairwiseQDiff K Q vertices hvertices))
    howned (Set.Subset.refl _) hc

end
end ElevenSquare.Tasks.T07
