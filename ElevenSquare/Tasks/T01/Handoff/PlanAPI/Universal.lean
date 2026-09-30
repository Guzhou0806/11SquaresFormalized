import ElevenSquare.Tasks.T01.Handoff.PlanAPI.Subtract
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.PolygonCorners
import ElevenSquare.Pending.S07_CellHalfplanes

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending
open ElevenSquare.Tasks.T01
open scoped Pointwise
noncomputable section

def qpointSubtract (a b : QPoint) : QPoint := (a.1 - b.1, a.2 - b.2)

def QPointPolygonCheck (p : QPoint) (polygon : Polygon) : Prop :=
  ∀ h ∈ polygon, h.a * p.1 + h.b * p.2 ≤ h.c

instance qpointPolygonCheckDecidable (p : QPoint) (polygon : Polygon) :
    Decidable (QPointPolygonCheck p polygon) := by
  unfold QPointPolygonCheck
  infer_instance

theorem qpoint_polygon_sound (p : QPoint) (polygon : Polygon)
    (hc : QPointPolygonCheck p polygon) : realPoint p ∈ polygon.carrier := by
  intro h hh
  have he := hc h hh
  dsimp [Halfplane.contains, realPoint]
  exact_mod_cast he

theorem realPoint_qpointSubtract (a b : QPoint) :
    realPoint (qpointSubtract a b) = realPoint a - realPoint b := by
  ext <;> simp [qpointSubtract, realPoint]

/-- One exact rational split bound per difference-polygon facet. For a facet
`h`, all target vertices have support at most `b`, and all partner-domain
vertices have support at least `b - h.c`. This proves every target-minus-domain
pair satisfies the facet without checking the Cartesian product explicitly. -/
def FacetSupportCheck (targetVertices domainVertices : List QPoint)
    (difference : Polygon) (bounds : List ℚ) : Prop :=
  difference.length = bounds.length ∧
  ∀ hb ∈ difference.zip bounds,
    (∀ f ∈ targetVertices,
      hb.1.a * f.1 + hb.1.b * f.2 ≤ hb.2) ∧
    (∀ d ∈ domainVertices,
      hb.2 - hb.1.c ≤ hb.1.a * d.1 + hb.1.b * d.2)

instance facetSupportCheckDecidable (targetVertices domainVertices : List QPoint)
    (difference : Polygon) (bounds : List ℚ) :
    Decidable (FacetSupportCheck targetVertices domainVertices difference bounds) := by
  unfold FacetSupportCheck
  infer_instance

theorem facet_support_check_sound (targetVertices domainVertices : List QPoint)
    (difference : Polygon) (bounds : List ℚ)
    (hc : FacetSupportCheck targetVertices domainVertices difference bounds)
    (f : QPoint) (hf : f ∈ targetVertices)
    (d : QPoint) (hd : d ∈ domainVertices) :
    QPointPolygonCheck (qpointSubtract f d) difference := by
  intro h hh
  induction difference generalizing bounds with
  | nil => simp at hh
  | cons face rest ih =>
    cases bounds with
    | nil => simp [FacetSupportCheck] at hc
    | cons b bounds =>
      have hfirst := hc.2 (face,b) (by simp)
      have htail : FacetSupportCheck targetVertices domainVertices rest bounds := by
        refine ⟨by simpa using hc.1, ?_⟩
        intro item hitem
        exact hc.2 item (by simp [hitem])
      rcases List.mem_cons.mp hh with rfl | hh
      · have hupper := hfirst.1 f hf
        have hlower := hfirst.2 d hd
        dsimp [qpointSubtract]
        linarith
      · exact ih bounds htail hh

/-- An exact finite check of every vertex pair extends over the full convex
center polygons, including all facets and boundary points. -/
theorem polygon_difference_from_vertices
    (F D M : Polygon) (fverts dverts : List QPoint)
    (hF : BaselinePolygonCheck fverts F)
    (hD : BaselinePolygonCheck dverts D)
    (hpairs : ∀ f ∈ fverts, ∀ d ∈ dverts,
      QPointPolygonCheck (qpointSubtract f d) M)
    (f d : Point) (hf : f ∈ F.carrier) (hd : d ∈ D.carrier) :
    f - d ∈ M.carrier := by
  let fset : Set Point := {p | ∃ v ∈ fverts, p = realPoint v}
  let dset : Set Point := {p | ∃ v ∈ dverts, p = realPoint v}
  have hcorner : fset - dset ⊆ M.carrier := by
    rintro x ⟨a, ⟨av, hav, rfl⟩, b, ⟨bv, hbv, rfl⟩, rfl⟩
    change realPoint av - realPoint bv ∈ M.carrier
    rw [← realPoint_qpointSubtract]
    exact qpoint_polygon_sound _ _ (hpairs av hav bv hbv)
  have hconv : convexHull ℝ (fset - dset) ⊆ M.carrier :=
    convexHull_min hcorner (polygon_convex M)
  have hfd : f ∈ rationalHull fverts := baseline_polygon_check_sound _ _ hF hf
  have hdd : d ∈ rationalHull dverts := baseline_polygon_check_sound _ _ hD hd
  apply hconv
  rw [convexHull_sub]
  exact ⟨f, hfd, d, hdd, rfl⟩

/-- A single partner row supplies a closed center domain and a strict core.
The `difference` polygon is an inner polygon of Q_partner − Q_current, checked
by direct convex witnesses at its vertices. All F/D vertex differences must
lie in that polygon. No archive success flag enters this predicate. -/
structure UniversalRowCertificate where
  domainVertices : List QPoint
  domainCorners : List (ℕ × ℕ)
  partnerCore : List QPoint
  differenceVertices : List QPoint
  differenceCorners : List (ℕ × ℕ)
  difference : Polygon
  witnesses : List DifferenceWitness

def UniversalRowCertificate.Check (c : UniversalRowCertificate)
    (currentCore regionVertices : List QPoint) (partnerRow : PoseRow) : Prop :=
  PolygonCornerCheck c.domainVertices partnerRow.centers c.domainCorners ∧
  (∀ v ∈ c.partnerCore, BaselineCoreVertexCheck v partnerRow.lo partnerRow.hi) ∧
  PolygonCornerCheck c.differenceVertices c.difference c.differenceCorners ∧
  DifferenceVerticesCheck c.partnerCore currentCore c.differenceVertices c.witnesses ∧
  (∀ f ∈ regionVertices, ∀ d ∈ c.domainVertices,
    QPointPolygonCheck (qpointSubtract f d) c.difference)

instance universalRowCertificateCheckDecidable
    (c : UniversalRowCertificate) (currentCore regionVertices : List QPoint)
    (partnerRow : PoseRow) : Decidable (c.Check currentCore regionVertices partnerRow) := by
  unfold UniversalRowCertificate.Check
  infer_instance

theorem universal_row_collision (c : UniversalRowCertificate)
    (currentCore regionVertices : List QPoint) (region : Polygon)
    (partnerRow : PoseRow) (hc : c.Check currentCore regionVertices partnerRow)
    (hregion : BaselinePolygonCheck regionVertices region)
    (q r : UnitSquare) (hr : partnerRow.contains r)
    (hqcore : CoreFits (rationalHull currentCore) q)
    (hcenter : q.center ∈ region.carrier) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  have hdiff : q.center - r.center ∈ c.difference.carrier :=
    polygon_difference_from_vertices region partnerRow.centers c.difference
      regionVertices c.domainVertices hregion
      (polygon_corner_check_sound _ _ _ hc.1) hc.2.2.2.2
      q.center r.center hcenter hr.1
  have hforbidden : q.center - r.center ∈
      forbiddenCenters (rationalHull c.partnerCore) (rationalHull currentCore) :=
    checked_forbidden_polygon c.partnerCore currentCore c.differenceVertices
      c.difference c.witnesses
      (polygon_corner_check_sound _ _ _ hc.2.2.1) hc.2.2.2.1 hdiff
  obtain ⟨vj, hvj, vi, hvi, hcenterEq⟩ := hforbidden
  have hrCore : CoreFits (rationalHull c.partnerCore) r := by
    apply baseline_row_core_checked partnerRow c.partnerCore hc.2.1
    exact hr
  refine ⟨q.center + vi, hqcore vi hvi, ?_⟩
  have heq : q.center + vi = r.center + vj := by
    ext
    · have he := congrArg Prod.fst hcenterEq
      dsimp at he ⊢
      linarith
    · have he := congrArg Prod.snd hcenterEq
      dsimp at he ⊢
      linarith
  rw [heq]
  exact hrCore vj hvj

/-- The support-bound version computes only O(facets × vertices) rational
inequalities rather than all target/domain vertex pairs. -/
structure UniversalSupportRowCertificate where
  domainVertices : List QPoint
  domainCorners : List (ℕ × ℕ)
  partnerCore : List QPoint
  differenceVertices : List QPoint
  differenceCorners : List (ℕ × ℕ)
  difference : Polygon
  witnesses : List DifferenceWitness
  facetBounds : List ℚ

def UniversalSupportRowCertificate.Check (c : UniversalSupportRowCertificate)
    (currentCore regionVertices : List QPoint) (partnerRow : PoseRow) : Prop :=
  PolygonCornerCheck c.domainVertices partnerRow.centers c.domainCorners ∧
  (∀ v ∈ c.partnerCore, BaselineCoreVertexCheck v partnerRow.lo partnerRow.hi) ∧
  PolygonCornerCheck c.differenceVertices c.difference c.differenceCorners ∧
  DifferenceVerticesCheck c.partnerCore currentCore c.differenceVertices c.witnesses ∧
  FacetSupportCheck regionVertices c.domainVertices c.difference c.facetBounds

instance universalSupportRowCertificateCheckDecidable
    (c : UniversalSupportRowCertificate) (currentCore regionVertices : List QPoint)
    (partnerRow : PoseRow) : Decidable (c.Check currentCore regionVertices partnerRow) := by
  unfold UniversalSupportRowCertificate.Check
  infer_instance

theorem universal_support_row_collision (c : UniversalSupportRowCertificate)
    (currentCore regionVertices : List QPoint) (region : Polygon)
    (partnerRow : PoseRow) (hc : c.Check currentCore regionVertices partnerRow)
    (hregion : BaselinePolygonCheck regionVertices region)
    (q r : UnitSquare) (hr : partnerRow.contains r)
    (hqcore : CoreFits (rationalHull currentCore) q)
    (hcenter : q.center ∈ region.carrier) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  let cert : UniversalRowCertificate :=
    { domainVertices := c.domainVertices
      domainCorners := c.domainCorners
      partnerCore := c.partnerCore
      differenceVertices := c.differenceVertices
      differenceCorners := c.differenceCorners
      difference := c.difference
      witnesses := c.witnesses }
  have hcert : cert.Check currentCore regionVertices partnerRow := by
    refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, ?_⟩
    intro f hf d hd
    exact facet_support_check_sound regionVertices c.domainVertices
      c.difference c.facetBounds hc.2.2.2.2 f hf d hd
  exact universal_row_collision cert currentCore regionVertices region
    partnerRow hcert hregion q r hr hqcore hcenter

/-- A partner row may have an empty center domain. Such a row is discharged
by a strict rational Farkas contradiction. Live rows carry the full strict
core and universal difference certificate. -/
inductive UniversalRowCase where
  | empty (witness : BaselineCombination)
  | live (certificate : UniversalRowCertificate)
  | support (certificate : UniversalSupportRowCertificate)

def UniversalRowCase.Check (c : UniversalRowCase)
    (currentCore regionVertices : List QPoint) (partnerRow : PoseRow) : Prop :=
  match c with
  | .empty w => BaselineStrictImplicationCheck partnerRow.centers baselineZeroHalfplane w
  | .live cert => cert.Check currentCore regionVertices partnerRow
  | .support cert => cert.Check currentCore regionVertices partnerRow

instance universalRowCaseCheckDecidable
    (c : UniversalRowCase) (currentCore regionVertices : List QPoint)
    (partnerRow : PoseRow) : Decidable (c.Check currentCore regionVertices partnerRow) := by
  cases c <;> unfold UniversalRowCase.Check <;> infer_instance

theorem universal_row_case_collision (c : UniversalRowCase)
    (currentCore regionVertices : List QPoint) (region : Polygon)
    (partnerRow : PoseRow) (hc : c.Check currentCore regionVertices partnerRow)
    (hregion : BaselinePolygonCheck regionVertices region)
    (q r : UnitSquare) (hr : partnerRow.contains r)
    (hqcore : CoreFits (rationalHull currentCore) q)
    (hcenter : q.center ∈ region.carrier) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  cases c with
  | empty w =>
    have hf := baseline_strict_implication_check_sound partnerRow.centers
      baselineZeroHalfplane w hc r.center hr.1
    norm_num [baselineZeroHalfplane] at hf
  | live cert =>
    exact universal_row_collision cert currentCore regionVertices region
      partnerRow hc hregion q r hr hqcore hcenter
  | support cert =>
    exact universal_support_row_collision cert currentCore regionVertices region
      partnerRow hc hregion q r hr hqcore hcenter

structure UniversalPiece where
  partner : Owner
  core : List QPoint
  vertices : List QPoint
  corners : List (ℕ × ℕ)
  polygon : Polygon
  partnerRows : List (PoseRow × UniversalRowCase)

def UniversalPiece.Check (s : PoseState) (i : Owner) (current : PoseRow)
    (p : UniversalPiece) : Prop :=
  i ≠ p.partner ∧
  PolygonCornerCheck p.vertices p.polygon p.corners ∧
  (∀ v ∈ p.core, BaselineCoreVertexCheck v current.lo current.hi) ∧
  p.partnerRows.map Prod.fst = s.rows p.partner ∧
  p.partnerRows.Forall (fun row => row.2.Check p.core p.vertices row.1)

instance universalPieceCheckDecidable
    (s : PoseState) (i : Owner) (current : PoseRow) (p : UniversalPiece) :
    Decidable (p.Check s i current) := by
  classical
  unfold UniversalPiece.Check
  infer_instance

theorem universal_piece_collision (s : PoseState) (i : Owner)
    (current : PoseRow) (p : UniversalPiece) (hc : p.Check s i current)
    (q r : UnitSquare) (hq : current.contains q)
    (hr : RowsContain (s.rows p.partner) r)
    (hcenter : q.center ∈ p.polygon.carrier) :
    ∃ x, OpenSquare q x ∧ OpenSquare r x := by
  obtain ⟨partnerRow, hmem, hcontains⟩ := hr
  rw [← hc.2.2.2.1] at hmem
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hmem
  have hqcore : CoreFits (rationalHull p.core) q :=
    baseline_row_core_checked current p.core hc.2.2.1 q hq
  exact universal_row_case_collision entry.2 p.core p.vertices p.polygon entry.1
    ((List.forall_iff_forall_mem).mp hc.2.2.2.2 entry he)
    (polygon_corner_check_sound _ _ _ hc.2.1) q r hcontains hqcore hcenter

def universalPruningOutput (plan : List (PoseRow × UniversalPiece)) : List PoseRow :=
  plan.bind (fun item => outsideRows item.1 item.2.polygon)

def UniversalPruningCheck (s : PoseState) (i : Owner)
    (plan : List (PoseRow × UniversalPiece)) : Prop :=
  plan.map Prod.fst = s.rows i ∧
  plan.Forall (fun item => item.2.Check s i item.1)

instance universalPruningCheckDecidable
    (s : PoseState) (i : Owner) (plan : List (PoseRow × UniversalPiece)) :
    Decidable (UniversalPruningCheck s i plan) := by
  classical
  unfold UniversalPruningCheck
  infer_instance

/-- The compact form of an archived sweep row: retained convex polygons and
universal collision polygons cover the predecessor domain. The large
intermediate residual partition need not be imported. The cover itself is
still certified by exact rational Farkas combinations. -/
structure UniversalRowPruningCertificate where
  kept : List Polygon
  direct : List ForbiddenPiece
  forbidden : List UniversalPiece
  cover : BaselineCoverCertificate

def UniversalRowPruningCertificate.targets (c : UniversalRowPruningCertificate) :
    List Polygon := c.kept ++ c.direct.map ForbiddenPiece.polygon ++
      c.forbidden.map UniversalPiece.polygon

def UniversalRowPruningCertificate.Check (s : PoseState) (i : Owner)
    (r : PoseRow) (c : UniversalRowPruningCertificate) : Prop :=
  c.cover.Check r.centers c.targets ∧
  c.direct.Forall (fun p => p.Check s i r) ∧
  c.forbidden.Forall (fun p => p.Check s i r)

instance universalRowPruningCertificateCheckDecidable
    (s : PoseState) (i : Owner) (r : PoseRow)
    (c : UniversalRowPruningCertificate) : Decidable (c.Check s i r) := by
  classical
  unfold UniversalRowPruningCertificate.Check
  infer_instance

def UniversalRowPruningCertificate.keptRows (r : PoseRow)
    (c : UniversalRowPruningCertificate) : List PoseRow :=
  c.kept.map (fun polygon => {r with centers := polygon})

/-- The forbidden branch is refuted using the actual partner square and its
actual covered row; no ownership premise or representative pose is substituted. -/
theorem universal_row_pruning_keeps {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (i : Owner) (r : PoseRow)
    (c : UniversalRowPruningCertificate) (hc : c.Check s i r)
    (hs : StateHolds P s) (hq : r.contains (P.squares i)) :
    RowsContain (c.keptRows r) (P.squares i) := by
  obtain ⟨polygon, hpoly, hcenter⟩ := baseline_cover_certificate_sound
    r.centers c.targets c.cover hc.1 (P.squares i).center hq.1
  rcases List.mem_append.mp hpoly with hleft | huniversal
  · rcases List.mem_append.mp hleft with hkept | hdirect
    · exact ⟨{r with centers := polygon},
        List.mem_map.mpr ⟨polygon, hkept, rfl⟩, hcenter, hq.2⟩
    · obtain ⟨piece, hmem, rfl⟩ := List.mem_map.mp hdirect
      have hp : piece.Check s i r :=
        (List.forall_iff_forall_mem).mp hc.2.1 piece hmem
      have hcore : CoreFits (rationalHull piece.core) (P.squares i) :=
        baseline_row_core_checked r piece.core hp.2.2.2 (P.squares i) hq
      have hbad : (P.squares i).center ∈
          forbiddenCenters (rationalHull (s.owned piece.partner))
            (rationalHull piece.core) :=
        checked_forbidden_polygon (s.owned piece.partner) piece.core
          piece.vertices piece.polygon piece.witnesses hp.2.1 hp.2.2.1 hcenter
      obtain ⟨point, hi, hj⟩ := forbidden_center_implies_overlap
        (P.squares i) (P.squares piece.partner)
        (rationalHull (s.owned piece.partner)) (rationalHull piece.core)
        (hs.2 piece.partner) hcore hbad
      exact False.elim (P.interior_disjoint i piece.partner hp.1 point ⟨hi, hj⟩)
  · obtain ⟨piece, hmem, rfl⟩ := List.mem_map.mp huniversal
    have hp : piece.Check s i r :=
      (List.forall_iff_forall_mem).mp hc.2.2 piece hmem
    obtain ⟨point, hi, hj⟩ := universal_piece_collision s i r piece hp
      (P.squares i) (P.squares piece.partner) hq (hs.1 piece.partner) hcenter
    exact False.elim (P.interior_disjoint i piece.partner hp.1 point ⟨hi, hj⟩)

def universalProgramOutput (plan : List (PoseRow × UniversalRowPruningCertificate)) :
    List PoseRow :=
  plan.bind (fun item => item.2.keptRows item.1)

def UniversalProgramCheck (s : PoseState) (i : Owner)
    (plan : List (PoseRow × UniversalRowPruningCertificate)) : Prop :=
  plan.map Prod.fst = s.rows i ∧
  plan.Forall (fun item => item.2.Check s i item.1)

instance universalProgramCheckDecidable
    (s : PoseState) (i : Owner)
    (plan : List (PoseRow × UniversalRowPruningCertificate)) :
    Decidable (UniversalProgramCheck s i plan) := by
  classical
  unfold UniversalProgramCheck
  infer_instance

theorem universal_program_sound {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (i : Owner)
    (plan : List (PoseRow × UniversalRowPruningCertificate))
    (hc : UniversalProgramCheck s i plan) (hs : StateHolds P s) :
    StateHolds P (replaceRows s i (universalProgramOutput plan)) := by
  refine ⟨?_, hs.2⟩
  intro j
  by_cases hj : j = i
  · subst j
    obtain ⟨r, hr, hcontains⟩ := hs.1 i
    rw [← hc.1] at hr
    obtain ⟨item, hm, rfl⟩ := List.mem_map.mp hr
    have hcheck := (List.forall_iff_forall_mem).mp hc.2 item hm
    obtain ⟨out, hout, hq⟩ :=
      universal_row_pruning_keeps P s i item.1 item.2 hcheck hs hcontains
    simpa only [replaceRows, Function.update_self] using
      (show RowsContain (universalProgramOutput plan) (P.squares i) from
        ⟨out, List.mem_bind.mpr ⟨item, hm, hout⟩, hq⟩)
  · simpa only [replaceRows, Function.update_of_ne hj] using hs.1 j

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.polygon_difference_from_vertices
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.facet_support_check_sound
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.universal_piece_collision
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.universal_program_sound
