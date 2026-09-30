import ElevenSquare.Tasks.T01.CaptureCover

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A row may force a singleton feature or every k-subset of a majority
feature. Each subset has its own small exact cover. The remaining singleton
pieces are ruled out by independently owned points. -/
abbrev MixedFeatureRowPlan :=
  List (Finset QPoint × CaptureCoverPlan × BaselineCoverCertificate)

theorem rationalHull_eq_of_toFinset_eq (vs ws : List QPoint)
    (he : vs.toFinset = ws.toFinset) : rationalHull vs = rationalHull ws := by
  have hmem (v : QPoint) : v ∈ vs ↔ v ∈ ws := by
    simpa using congrArg (fun s : Finset QPoint => v ∈ s) he
  unfold rationalHull
  apply congrArg (convexHull ℝ)
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, (hmem v).mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, (hmem v).mpr hv, rfl⟩

def MixedFeatureRowCheck (point : QPoint) (sites : Finset QPoint) (k : ℕ)
    (blocked : List QPoint) (r : PoseRow) (plan : MixedFeatureRowPlan) : Prop :=
  ∀ J ∈ sites.powersetCard k, ∃ item ∈ plan,
    item.1 = J ∧ CaptureCoverCheck r item.2.1 item.2.2 ∧
      ∀ piece ∈ item.2.1,
        piece.1.toFinset = J ∨ piece.1 = [point] ∨
          ∃ p ∈ blocked, piece.1 = [p]

instance (point : QPoint) (sites : Finset QPoint) (k : ℕ)
    (blocked : List QPoint) (r : PoseRow) (plan : MixedFeatureRowPlan) :
    Decidable (MixedFeatureRowCheck point sites k blocked r plan) := by
  classical
  unfold MixedFeatureRowCheck
  infer_instance

theorem mixed_feature_row_sound (point : QPoint) (sites : Finset QPoint)
    (k : ℕ) (blocked : List QPoint) (r : PoseRow)
    (plan : MixedFeatureRowPlan)
    (hc : MixedFeatureRowCheck point sites k blocked r plan)
    (q : UnitSquare) (hq : r.contains q)
    (hb : ∀ p ∈ blocked, ¬ OpenSquare q (realPoint p)) :
    OpenSquare q (realPoint point) ∨ BaselineMajorityCapture sites k q := by
  by_cases hp : OpenSquare q (realPoint point)
  · exact Or.inl hp
  right
  intro J hJ
  obtain ⟨item, _, _, hcheck, hclass⟩ := hc J hJ
  obtain ⟨piece, hpiece, hcap⟩ :=
    checked_capture_cover r item.2.1 item.2.2 hcheck q hq
  rcases hclass piece hpiece with hmajor | hsingle | ⟨p, hmem, hsingle⟩
  · rwa [rationalHull_eq_of_toFinset_eq piece.1 J.toList (by simpa using hmajor)] at hcap
  · have h : OpenSquare q (realPoint point) := by
      apply singleton_capture point q
      simpa only [hsingle] using hcap
    exact False.elim (hp h)
  · have h : OpenSquare q (realPoint p) := by
      apply singleton_capture p q
      simpa only [hsingle] using hcap
    exact False.elim (hb p hmem h)

/-- A packing turns distinct-owner captures of the blocked points into the
exclusions needed by the row theorem. -/
theorem mixed_feature_packing_row_sound {S : ℝ} (P : Packing 11 S)
    (i : Owner) (point : QPoint) (sites : Finset QPoint) (k : ℕ)
    (blocked : List QPoint) (r : PoseRow) (plan : MixedFeatureRowPlan)
    (hc : MixedFeatureRowCheck point sites k blocked r plan)
    (hq : r.contains (P.squares i))
    (howned : ∀ p ∈ blocked, ∃ j : Owner,
      i ≠ j ∧ OpenSquare (P.squares j) (realPoint p)) :
    OpenSquare (P.squares i) (realPoint point) ∨
      BaselineMajorityCapture sites k (P.squares i) := by
  apply mixed_feature_row_sound point sites k blocked r plan hc _ hq
  intro p hm hp
  obtain ⟨j, hij, hj⟩ := howned p hm
  exact P.interior_disjoint i j hij (realPoint p) ⟨hp, hj⟩

/-- A blocked point is justified by a finite rational hull expression in an
already owned hull, with the other owner recorded explicitly. -/
structure OwnedBlock where
  point : QPoint
  partner : Owner
  witness : HullWitness

def OwnedBlock.Check (s : PoseState) (i : Owner) (b : OwnedBlock) : Prop :=
  i ≠ b.partner ∧ b.witness.Valid (s.owned b.partner) ∧
    b.witness.eval (s.owned b.partner) = b.point

instance (s : PoseState) (i : Owner) (b : OwnedBlock) : Decidable (b.Check s i) := by
  unfold OwnedBlock.Check
  infer_instance

structure MixedFeatureRowCertificate where
  blocks : List OwnedBlock
  plan : MixedFeatureRowPlan

def MixedFeatureRowCertificate.Check (s : PoseState) (i : Owner)
    (point : QPoint) (sites : Finset QPoint) (k : ℕ) (r : PoseRow)
    (c : MixedFeatureRowCertificate) : Prop :=
  MixedFeatureRowCheck point sites k (c.blocks.map OwnedBlock.point) r c.plan ∧
    c.blocks.Forall (fun b => b.Check s i)

instance (s : PoseState) (i : Owner) (point : QPoint)
    (sites : Finset QPoint) (k : ℕ) (r : PoseRow)
    (c : MixedFeatureRowCertificate) : Decidable (c.Check s i point sites k r) := by
  unfold MixedFeatureRowCertificate.Check
  infer_instance

theorem mixed_feature_certificate_sound {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (hs : StateHolds P s) (i : Owner) (point : QPoint)
    (sites : Finset QPoint) (k : ℕ) (r : PoseRow)
    (c : MixedFeatureRowCertificate) (hc : c.Check s i point sites k r)
    (hq : r.contains (P.squares i)) :
    OpenSquare (P.squares i) (realPoint point) ∨
      BaselineMajorityCapture sites k (P.squares i) := by
  apply mixed_feature_packing_row_sound P i point sites k
    (c.blocks.map OwnedBlock.point) r c.plan hc.1 hq
  intro p hp
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
  have hcheck : b.Check s i := (List.forall_iff_forall_mem).mp hc.2 b hb
  refine ⟨b.partner, hcheck.1, ?_⟩
  have hmember : realPoint b.point ∈ rationalHull (s.owned b.partner) := by
    rw [← hcheck.2.2]
    exact hullWitness_sound (s.owned b.partner) b.witness hcheck.2.1
  exact hs.2 b.partner hmember

/-- Three distinct squares cannot all capture one of two capacity-one
features. The second feature is a geometric majority, with its capacity
proved by separation rather than assumed from the archived flags. -/
theorem mixed_three_impossible {S : ℝ} (P : Packing 11 S)
    (point : QPoint) (sites : Finset QPoint) (k : ℕ)
    (hsize : sites.card + 1 = 2 * k)
    (owners : Fin 3 → Owner) (hinj : Function.Injective owners)
    (hcap : ∀ j : Fin 3,
      OpenSquare (P.squares (owners j)) (realPoint point) ∨
        BaselineMajorityCapture sites k (P.squares (owners j))) : False := by
  classical
  have hex : ∀ j : Fin 3, ∃ f : Fin 2,
      (if f = 0 then OpenSquare (P.squares (owners j)) (realPoint point)
       else BaselineMajorityCapture sites k (P.squares (owners j))) := by
    intro j
    rcases hcap j with hp | hm
    · exact ⟨0, hp⟩
    · exact ⟨1, hm⟩
  choose assigned hassigned using hex
  have hunique (f : Fin 2) (i j : Owner)
      (hi : if f = 0 then OpenSquare (P.squares i) (realPoint point)
            else BaselineMajorityCapture sites k (P.squares i))
      (hj : if f = 0 then OpenSquare (P.squares j) (realPoint point)
            else BaselineMajorityCapture sites k (P.squares j)) : i = j := by
    fin_cases f
    · by_contra hne
      exact P.interior_disjoint i j hne (realPoint point) ⟨hi, hj⟩
    · exact baseline_majority_unique_owner P sites k hsize i j hi hj
  have ha : Function.Injective assigned := by
    intro j l heq
    apply hinj
    exact hunique (assigned j) (owners j) (owners l)
      (hassigned j) (heq ▸ hassigned l)
  have hc : Fintype.card (Fin 3) ≤ Fintype.card (Fin 2) :=
    Fintype.card_le_of_injective assigned ha
  norm_num at hc

structure MixedThreePlan where
  point : QPoint
  sites : Finset QPoint
  threshold : ℕ
  owners : Fin 3 → Owner
  rows : Fin 3 → List (PoseRow × MixedFeatureRowCertificate)

def MixedThreePlan.Check (s : PoseState) (c : MixedThreePlan) : Prop :=
  c.sites.card + 1 = 2 * c.threshold ∧
  Function.Injective c.owners ∧
  ∀ j : Fin 3,
    (c.rows j).map Prod.fst = s.rows (c.owners j) ∧
    ∀ item ∈ c.rows j,
      item.2.Check s (c.owners j) c.point c.sites c.threshold item.1

instance (s : PoseState) (c : MixedThreePlan) : Decidable (c.Check s) := by
  classical
  unfold MixedThreePlan.Check
  infer_instance

theorem mixed_three_plan_refutes {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (c : MixedThreePlan) (hc : c.Check s)
    (hs : StateHolds P s) : False := by
  apply mixed_three_impossible P c.point c.sites c.threshold hc.1 c.owners hc.2.1
  intro j
  obtain ⟨r, hr, hq⟩ := hs.1 (c.owners j)
  rw [← (hc.2.2 j).1] at hr
  obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hr
  exact mixed_feature_certificate_sound P s hs (c.owners j) c.point c.sites
    c.threshold item.1 item.2 ((hc.2.2 j).2 item hi) hq

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.mixed_three_plan_refutes
