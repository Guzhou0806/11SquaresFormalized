import ElevenSquare.Tasks.T01.Handoff.PlanAPI.WeightedFeature
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MixedFeature

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- An exact finite cover of a center region proving one feature. Majority
features require one checked cover for every threshold-sized subset. -/
structure WeightedFeatureRegionCertificate where
  subsetCovers : List (Finset QPoint × FeatureCoverCertificate)

def WeightedFeatureRegionCertificate.Check (s : PoseState) (i : Owner)
    (r : PoseRow) (target : WeightedTarget)
    (c : WeightedFeatureRegionCertificate) : Prop :=
  match target with
  | .point p => ∃ item ∈ c.subsetCovers,
      item.1 = {p} ∧ item.2.Check s i [p] r
  | .majority sites k => ∀ J ∈ sites.powersetCard k,
      ∃ item ∈ c.subsetCovers,
        item.1 = J ∧ item.2.Check s i J.toList r

instance weightedFeatureRegionCertificateCheckDecidable
    (s : PoseState) (i : Owner) (r : PoseRow) (target : WeightedTarget)
    (c : WeightedFeatureRegionCertificate) : Decidable (c.Check s i r target) := by
  cases target <;> dsimp [WeightedFeatureRegionCertificate.Check] <;> infer_instance

theorem weighted_feature_region_sound {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (hs : StateHolds P s) (i : Owner) (r : PoseRow)
    (target : WeightedTarget) (c : WeightedFeatureRegionCertificate)
    (hc : c.Check s i r target) (hq : r.contains (P.squares i)) :
    target.Capture (P.squares i) := by
  cases target with
  | point p =>
    obtain ⟨item, _, hitem, hcheck⟩ := hc
    exact singleton_capture p (P.squares i)
      (by simpa using feature_cover_sound P s hs i [p] r item.2 hcheck hq)
  | majority sites k =>
    intro J hJ
    obtain ⟨item, _, _, hcheck⟩ := hc J hJ
    exact feature_cover_sound P s hs i J.toList r item.2 hcheck hq

/-- A center region with exact certificates for enough weighted features. -/
structure WeightedChargeRegion (n : ℕ) where
  polygon : Polygon
  captured : Finset (Fin n)
  certificates : List (Fin n × WeightedFeatureRegionCertificate)

def WeightedChargeRegion.Check {n : ℕ} (features : Fin n → WeightedFeature)
    (s : PoseState) (i : Owner) (r : PoseRow) (threshold : ℕ)
    (c : WeightedChargeRegion n) : Prop :=
  threshold ≤ ∑ f ∈ c.captured, (features f).weight ∧
  ∀ f ∈ c.captured, ∃ item ∈ c.certificates,
    item.1 = f ∧ item.2.Check s i {r with centers := c.polygon} (features f).target

instance weightedChargeRegionCheckDecidable {n : ℕ}
    (features : Fin n → WeightedFeature) (s : PoseState) (i : Owner)
    (r : PoseRow) (threshold : ℕ) (c : WeightedChargeRegion n) :
    Decidable (c.Check features s i r threshold) := by
  classical
  unfold WeightedChargeRegion.Check
  infer_instance

theorem weighted_charge_region_sound {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (hs : StateHolds P s) {n : ℕ}
    (features : Fin n → WeightedFeature) (i : Owner) (r : PoseRow)
    (threshold : ℕ) (c : WeightedChargeRegion n)
    (hc : c.Check features s i r threshold)
    (hq : r.contains (P.squares i))
    (hpoly : (P.squares i).center ∈ c.polygon.carrier) :
    threshold ≤ weightedCharge features (P.squares i) := by
  classical
  have hcaptured (f : Fin n) (hf : f ∈ c.captured) :
      (features f).Capture (P.squares i) := by
    obtain ⟨item, _, hitem, hcheck⟩ := hc.2 f hf
    exact weighted_feature_region_sound P s hs i
      {r with centers := c.polygon} (features f).target item.2 hcheck
      ⟨hpoly, hq.2⟩
  calc
    threshold ≤ ∑ f ∈ c.captured, (features f).weight := hc.1
    _ = ∑ f ∈ c.captured, featureCharge (features f) (P.squares i) := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [featureCharge, hcaptured f hf]
    _ ≤ weightedCharge features (P.squares i) := by
      unfold weightedCharge
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro f _ _
      exact Nat.zero_le _

/-- A singleton capture region certified as already owned by another square.
This keeps a simple point blocker independent of the partner's entire owned
hull and reuses the same exact capture geometry as packet singleton features. -/
structure WeightedOwnedBlockPiece where
  block : OwnedBlock
  capture : FeatureCapturePiece

def WeightedOwnedBlockPiece.polygon (piece : WeightedOwnedBlockPiece) : Polygon :=
  piece.capture.polygon

def WeightedOwnedBlockPiece.Check (s : PoseState) (i : Owner)
    (r : PoseRow) (piece : WeightedOwnedBlockPiece) : Prop :=
  piece.block.Check s i ∧ piece.capture.Check [piece.block.point] r

instance weightedOwnedBlockPieceCheckDecidable (s : PoseState) (i : Owner)
    (r : PoseRow) (piece : WeightedOwnedBlockPiece) :
    Decidable (piece.Check s i r) := by
  unfold WeightedOwnedBlockPiece.Check
  infer_instance

theorem weighted_owned_block_piece_impossible {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (hs : StateHolds P s) (i : Owner) (r : PoseRow)
    (piece : WeightedOwnedBlockPiece) (hc : piece.Check s i r)
    (hq : r.contains (P.squares i))
    (hpoly : (P.squares i).center ∈ piece.polygon.carrier) : False := by
  have hi : OpenSquare (P.squares i) (realPoint piece.block.point) :=
    singleton_capture piece.block.point (P.squares i)
      (feature_capture_piece_sound [piece.block.point] r piece.capture
        hc.2 (P.squares i) hq hpoly)
  have hmember : realPoint piece.block.point ∈
      rationalHull (s.owned piece.block.partner) := by
    rw [← hc.1.2.2]
    exact hullWitness_sound (s.owned piece.block.partner) piece.block.witness
      hc.1.2.1
  have hj : OpenSquare (P.squares piece.block.partner)
      (realPoint piece.block.point) := hs.2 piece.block.partner hmember
  exact P.interior_disjoint i piece.block.partner hc.1.1
    (realPoint piece.block.point) ⟨hi, hj⟩

/-- Exact row cover by charged center regions and impossible direct overlap
regions. Every region proves its packet threshold before the global capacity
count is used. -/
structure WeightedRowCertificate (n : ℕ) where
  chargeRegions : List (WeightedChargeRegion n)
  forbidden : List ForbiddenPiece
  ownedBlocks : List WeightedOwnedBlockPiece
  cover : BaselineCoverCertificate

def WeightedRowCertificate.targets {n : ℕ} (c : WeightedRowCertificate n) :
    List Polygon :=
  c.chargeRegions.map WeightedChargeRegion.polygon ++
    c.forbidden.map ForbiddenPiece.polygon ++
    c.ownedBlocks.map WeightedOwnedBlockPiece.polygon

def WeightedRowCertificate.Check {n : ℕ}
    (features : Fin n → WeightedFeature) (s : PoseState) (i : Owner)
    (r : PoseRow) (threshold : ℕ) (c : WeightedRowCertificate n) : Prop :=
  c.cover.Check r.centers c.targets ∧
  (∀ region ∈ c.chargeRegions, region.Check features s i r threshold) ∧
  (∀ piece ∈ c.forbidden, piece.Check s i r) ∧
  ∀ piece ∈ c.ownedBlocks, piece.Check s i r

instance weightedRowCertificateCheckDecidable {n : ℕ}
    (features : Fin n → WeightedFeature) (s : PoseState) (i : Owner)
    (r : PoseRow) (threshold : ℕ) (c : WeightedRowCertificate n) :
    Decidable (c.Check features s i r threshold) := by
  unfold WeightedRowCertificate.Check
  infer_instance

theorem weighted_row_sound {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (hs : StateHolds P s) {n : ℕ}
    (features : Fin n → WeightedFeature) (i : Owner) (r : PoseRow)
    (threshold : ℕ) (c : WeightedRowCertificate n)
    (hc : c.Check features s i r threshold)
    (hq : r.contains (P.squares i)) :
    threshold ≤ weightedCharge features (P.squares i) := by
  obtain ⟨polygon, hmem, hcenter⟩ := baseline_cover_certificate_sound
    r.centers c.targets c.cover hc.1 (P.squares i).center hq.1
  rcases List.mem_append.mp hmem with hleft | hblock
  · rcases List.mem_append.mp hleft with hregion | hforbidden
    · obtain ⟨region, hr, rfl⟩ := List.mem_map.mp hregion
      exact weighted_charge_region_sound P s hs features i r threshold region
        (hc.2.1 region hr) hq hcenter
    · obtain ⟨piece, hm, rfl⟩ := List.mem_map.mp hforbidden
      have hv := hc.2.2.1 piece hm
      have hf := checked_forbidden_polygon (s.owned piece.partner) piece.core
        piece.vertices piece.polygon piece.witnesses hv.2.1 hv.2.2.1 hcenter
      have hcore := baseline_row_core_checked r piece.core hv.2.2.2 _ hq
      obtain ⟨p, hpi, hpj⟩ := forbidden_center_implies_overlap _ _ _ _
        (hs.2 piece.partner) hcore hf
      exact False.elim (P.interior_disjoint i piece.partner hv.1 p ⟨hpi, hpj⟩)
  · obtain ⟨piece, hm, rfl⟩ := List.mem_map.mp hblock
    exact False.elim (weighted_owned_block_piece_impossible P s hs i r piece
      (hc.2.2.2 piece hm) hq hcenter)

/-- The common packet checker for any finite mix of weighted singleton and
majority features. -/
structure WeightedFieldPlan (n : ℕ) where
  features : Fin n → WeightedFeature
  active : Finset Owner
  thresholds : Owner → ℕ
  rows : Owner → List (PoseRow × WeightedRowCertificate n)

def WeightedFieldPlan.Check {n : ℕ} (s : PoseState)
    (c : WeightedFieldPlan n) : Prop :=
  (∀ f, (c.features f).Valid) ∧
  weightedBudget c.features < ∑ i ∈ c.active, c.thresholds i ∧
  ∀ i ∈ c.active,
    (c.rows i).map Prod.fst = s.rows i ∧
    ∀ item ∈ c.rows i,
      item.2.Check c.features s i item.1 (c.thresholds i)

instance weightedFieldPlanCheckDecidable {n : ℕ} (s : PoseState)
    (c : WeightedFieldPlan n) : Decidable (c.Check s) := by
  classical
  unfold WeightedFieldPlan.Check
  infer_instance

theorem weighted_field_plan_refutes {S : ℝ} (P : Packing 11 S)
    (s : PoseState) {n : ℕ} (c : WeightedFieldPlan n)
    (hc : c.Check s) (hs : StateHolds P s) : False := by
  have hcharge (i : Owner) (hi : i ∈ c.active) :
      c.thresholds i ≤ weightedCharge c.features (P.squares i) := by
    obtain ⟨r, hr, hq⟩ := hs.1 i
    have hrow := (hc.2.2 i hi).1
    rw [← hrow] at hr
    obtain ⟨item, hm, rfl⟩ := List.mem_map.mp hr
    exact weighted_row_sound P s hs c.features i item.1 (c.thresholds i)
      item.2 ((hc.2.2 i hi).2 item hm) hq
  have hsum : (∑ i ∈ c.active, c.thresholds i) ≤
      ∑ i ∈ c.active, weightedCharge c.features (P.squares i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hcharge i hi
  have hcapacity := weighted_capacity P c.features hc.1 c.active
  have hbudget : weightedBudget c.features <
      ∑ i ∈ c.active, c.thresholds i := hc.2.1
  omega

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.weighted_field_plan_refutes
