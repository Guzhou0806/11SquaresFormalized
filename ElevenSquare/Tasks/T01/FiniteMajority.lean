import ElevenSquare.Tasks.T01.FinitePruning
import ElevenSquare.Tasks.T01.Majority

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

structure FeatureCapturePiece where
  core : List QPoint
  vertices : List QPoint
  polygon : Polygon
  witnesses : List DifferenceWitness

def FeatureCapturePiece.Check (feature : List QPoint) (r : PoseRow)
    (piece : FeatureCapturePiece) : Prop :=
  BaselinePolygonCheck piece.vertices piece.polygon ∧
  DifferenceVerticesCheck feature piece.core piece.vertices piece.witnesses ∧
  ∀ v ∈ piece.core, BaselineCoreVertexCheck v r.lo r.hi

instance featureCapturePieceCheckDecidable (feature : List QPoint) (r : PoseRow)
    (piece : FeatureCapturePiece) : Decidable (piece.Check feature r) := by
  unfold FeatureCapturePiece.Check
  infer_instance

theorem feature_capture_piece_sound (feature : List QPoint) (r : PoseRow)
    (piece : FeatureCapturePiece) (hc : piece.Check feature r)
    (q : UnitSquare) (hq : r.contains q) (hp : q.center ∈ piece.polygon.carrier) :
    ∃ p ∈ rationalHull feature, OpenSquare q p := by
  have hf := checked_forbidden_polygon feature piece.core piece.vertices piece.polygon
    piece.witnesses hc.1 hc.2.1 hp
  obtain ⟨p, hpf, v, hv, he⟩ := hf
  have ho := baseline_row_core_checked r piece.core hc.2.2 q hq v hv
  refine ⟨p, hpf, ?_⟩
  rw [he] at ho
  simpa only [sub_add_cancel] using ho

structure FeatureCoverCertificate where
  captures : List FeatureCapturePiece
  forbidden : List ForbiddenPiece
  cover : BaselineCoverCertificate

def FeatureCoverCertificate.targets (c : FeatureCoverCertificate) : List Polygon :=
  c.captures.map FeatureCapturePiece.polygon ++ c.forbidden.map ForbiddenPiece.polygon

def FeatureCoverCertificate.Check (s : PoseState) (i : Owner) (feature : List QPoint)
    (r : PoseRow) (c : FeatureCoverCertificate) : Prop :=
  c.cover.Check r.centers c.targets ∧
  (∀ piece ∈ c.captures, piece.Check feature r) ∧
  ∀ piece ∈ c.forbidden, piece.Check s i r

instance featureCoverCertificateCheckDecidable (s : PoseState) (i : Owner)
    (feature : List QPoint) (r : PoseRow) (c : FeatureCoverCertificate) :
    Decidable (c.Check s i feature r) := by
  unfold FeatureCoverCertificate.Check
  infer_instance

/-- A covered row either captures the feature or would overlap a distinct
owner. Only the latter alternative uses the state's previously proved hulls. -/
theorem feature_cover_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (hs : StateHolds P s) (i : Owner) (feature : List QPoint) (r : PoseRow)
    (c : FeatureCoverCertificate) (hc : c.Check s i feature r)
    (hq : r.contains (P.squares i)) :
    ∃ p ∈ rationalHull feature, OpenSquare (P.squares i) p := by
  obtain ⟨poly, hpoly, hp⟩ := baseline_cover_certificate_sound r.centers c.targets
    c.cover hc.1 (P.squares i).center hq.1
  rcases List.mem_append.mp hpoly with hcap | hforbid
  · obtain ⟨piece, hm, rfl⟩ := List.mem_map.mp hcap
    exact feature_capture_piece_sound feature r piece (hc.2.1 piece hm) _ hq hp
  · obtain ⟨piece, hm, rfl⟩ := List.mem_map.mp hforbid
    have hv := hc.2.2 piece hm
    have hf := checked_forbidden_polygon (s.owned piece.partner) piece.core
      piece.vertices piece.polygon piece.witnesses hv.2.1 hv.2.2.1 hp
    have hcore := baseline_row_core_checked r piece.core hv.2.2.2 _ hq
    obtain ⟨p, hpi, hpj⟩ := forbidden_center_implies_overlap _ _ _ _
      (hs.2 piece.partner) hcore hf
    exact False.elim (P.interior_disjoint i piece.partner hv.1 p ⟨hpi, hpj⟩)

abbrev MajorityRowPlan := List (Finset QPoint × FeatureCoverCertificate)

def MajorityRowCheck (sites : Finset QPoint) (k : ℕ) (s : PoseState) (i : Owner)
    (r : PoseRow) (plan : MajorityRowPlan) : Prop :=
  ∀ J ∈ sites.powersetCard k, ∃ item ∈ plan,
    item.1 = J ∧ item.2.Check s i J.toList r

instance majorityRowCheckDecidable (sites : Finset QPoint) (k : ℕ) (s : PoseState)
    (i : Owner) (r : PoseRow) (plan : MajorityRowPlan) :
    Decidable (MajorityRowCheck sites k s i r plan) := by
  unfold MajorityRowCheck
  infer_instance

theorem majority_row_checked {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (hs : StateHolds P s) (sites : Finset QPoint) (k : ℕ) (i : Owner)
    (r : PoseRow) (plan : MajorityRowPlan) (hc : MajorityRowCheck sites k s i r plan)
    (hq : r.contains (P.squares i)) : BaselineMajorityCapture sites k (P.squares i) := by
  intro J hJ
  obtain ⟨item, _, _, hitem⟩ := hc J hJ
  exact feature_cover_sound P s hs i J.toList r item.2 hitem hq

theorem majority_owner_checked {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (hs : StateHolds P s) (sites : Finset QPoint) (k : ℕ) (i : Owner)
    (plan : List (PoseRow × MajorityRowPlan))
    (hrows : plan.map Prod.fst = s.rows i)
    (hc : ∀ item ∈ plan, MajorityRowCheck sites k s i item.1 item.2) :
    BaselineMajorityCapture sites k (P.squares i) := by
  obtain ⟨r, hr, hq⟩ := hs.1 i
  rw [← hrows] at hr
  obtain ⟨item, hm, rfl⟩ := List.mem_map.mp hr
  exact majority_row_checked P s hs sites k i item.1 item.2 (hc item hm) hq

end
end ElevenSquare.Tasks.T01
