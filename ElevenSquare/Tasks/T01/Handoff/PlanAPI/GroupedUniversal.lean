import ElevenSquare.Tasks.T01.Handoff.PlanAPI.Universal

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01
noncomputable section

/-- A support certificate checked on a superset of domain vertices applies to
any subset. This lets several partner angle rows share the target-side facet
checks and the same strict difference kernel. -/
theorem facet_support_domain_subset (F D allD : List QPoint)
    (M : Polygon) (bounds : List ℚ)
    (hc : FacetSupportCheck F allD M bounds)
    (hsub : ∀ d ∈ D, d ∈ allD) :
    FacetSupportCheck F D M bounds := by
  refine ⟨hc.1, ?_⟩
  intro hb hh
  obtain ⟨hu, hl⟩ := hc.2 hb hh
  exact ⟨hu, fun d hd => hl d (hsub d hd)⟩

/-- A member supplies its exact closed domain and certifies that one common
partner core fits strictly for its complete angle interval. -/
structure GroupedPartnerMember where
  domainVertices : List QPoint
  domainCorners : List (ℕ × ℕ)

def GroupedPartnerMember.Check (m : GroupedPartnerMember)
    (core : List QPoint) (row : PoseRow) : Prop :=
  PolygonCornerCheck m.domainVertices row.centers m.domainCorners ∧
  ∀ v ∈ core, BaselineCoreVertexCheck v row.lo row.hi

instance groupedPartnerMemberCheckDecidable
    (m : GroupedPartnerMember) (core : List QPoint) (row : PoseRow) :
    Decidable (m.Check core row) := by
  unfold GroupedPartnerMember.Check
  infer_instance

/-- A single conservative inner difference polygon and one support split are
shared by a finite family of partner angle rows. Their domain vertices are
concatenated; every domain point lies in the hull of that finite union. -/
structure GroupedUniversalCertificate where
  partnerCore : List QPoint
  differenceVertices : List QPoint
  differenceCorners : List (ℕ × ℕ)
  difference : Polygon
  witnesses : List DifferenceWitness
  facetBounds : List ℚ
  members : List (PoseRow × GroupedPartnerMember)

def GroupedUniversalCertificate.domainVertices
    (c : GroupedUniversalCertificate) : List QPoint :=
  c.members.flatMap (fun item => item.2.domainVertices)

def GroupedUniversalCertificate.Check (c : GroupedUniversalCertificate)
    (currentCore regionVertices : List QPoint) : Prop :=
  PolygonCornerCheck c.differenceVertices c.difference c.differenceCorners ∧
  DifferenceVerticesCheck c.partnerCore currentCore
    c.differenceVertices c.witnesses ∧
  FacetSupportCheck regionVertices c.domainVertices c.difference c.facetBounds ∧
  c.members.Forall (fun item => item.2.Check c.partnerCore item.1)

instance groupedUniversalCertificateCheckDecidable
    (c : GroupedUniversalCertificate) (currentCore regionVertices : List QPoint) :
    Decidable (c.Check currentCore regionVertices) := by
  classical
  unfold GroupedUniversalCertificate.Check GroupedUniversalCertificate.domainVertices
  infer_instance

theorem grouped_universal_row_collision (c : GroupedUniversalCertificate)
    (currentCore regionVertices : List QPoint) (region : Polygon)
    (hc : c.Check currentCore regionVertices)
    (hregion : BaselinePolygonCheck regionVertices region)
    (item : PoseRow × GroupedPartnerMember) (hitem : item ∈ c.members)
    (q r : UnitSquare) (hr : item.1.contains r)
    (hqcore : CoreFits (rationalHull currentCore) q)
    (hcenter : q.center ∈ region.carrier) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  have hm : item.2.Check c.partnerCore item.1 :=
    (List.forall_iff_forall_mem).mp hc.2.2.2 item hitem
  let cert : UniversalSupportRowCertificate :=
    { domainVertices := item.2.domainVertices
      domainCorners := item.2.domainCorners
      partnerCore := c.partnerCore
      differenceVertices := c.differenceVertices
      differenceCorners := c.differenceCorners
      difference := c.difference
      witnesses := c.witnesses
      facetBounds := c.facetBounds }
  have hcert : cert.Check currentCore regionVertices item.1 := by
    refine ⟨hm.1, hm.2, hc.1, hc.2.1, ?_⟩
    exact facet_support_domain_subset regionVertices item.2.domainVertices
      c.domainVertices c.difference c.facetBounds hc.2.2.1
      (fun d hd => by
        change d ∈ c.members.flatMap (fun x => x.2.domainVertices)
        exact List.mem_flatMap.mpr ⟨item, hitem, hd⟩)
  exact universal_support_row_collision cert currentCore regionVertices region
    item.1 hcert hregion q r hr hqcore hcenter

/-- Group membership is checked against the *entire* predecessor pose family.
The grouped certificates therefore still cover every actual partner pose. -/
structure GroupedUniversalPiece where
  partner : Owner
  currentCore : List QPoint
  vertices : List QPoint
  corners : List (ℕ × ℕ)
  polygon : Polygon
  groups : List GroupedUniversalCertificate

def GroupedUniversalPiece.Check (s : PoseState) (i : Owner)
    (current : PoseRow) (p : GroupedUniversalPiece) : Prop :=
  i ≠ p.partner ∧
  PolygonCornerCheck p.vertices p.polygon p.corners ∧
  (∀ v ∈ p.currentCore,
    BaselineCoreVertexCheck v current.lo current.hi) ∧
  (p.groups.flatMap (fun g => g.members.map Prod.fst)) = s.rows p.partner ∧
  p.groups.Forall (fun g => g.Check p.currentCore p.vertices)

instance groupedUniversalPieceCheckDecidable
    (s : PoseState) (i : Owner) (current : PoseRow)
    (p : GroupedUniversalPiece) : Decidable (p.Check s i current) := by
  classical
  unfold GroupedUniversalPiece.Check
  infer_instance

theorem grouped_universal_piece_collision (s : PoseState) (i : Owner)
    (current : PoseRow) (p : GroupedUniversalPiece)
    (hc : p.Check s i current)
    (q r : UnitSquare) (hq : current.contains q)
    (hr : RowsContain (s.rows p.partner) r)
    (hcenter : q.center ∈ p.polygon.carrier) :
    ∃ x, OpenSquare q x ∧ OpenSquare r x := by
  obtain ⟨partnerRow, hrow, hcontains⟩ := hr
  rw [← hc.2.2.2.1] at hrow
  obtain ⟨group, hgroup, hrow⟩ := List.mem_flatMap.mp hrow
  obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hrow
  subst partnerRow
  have hqcore : CoreFits (rationalHull p.currentCore) q :=
    baseline_row_core_checked current p.currentCore hc.2.2.1 q hq
  exact grouped_universal_row_collision group p.currentCore p.vertices
    p.polygon ((List.forall_iff_forall_mem).mp hc.2.2.2.2 group hgroup)
    (polygon_corner_check_sound _ _ _ hc.2.1) item hitem
    q r hcontains hqcore hcenter

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.grouped_universal_piece_collision
