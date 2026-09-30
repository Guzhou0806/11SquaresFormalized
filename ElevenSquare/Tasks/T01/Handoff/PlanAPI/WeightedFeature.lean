import ElevenSquare.Tasks.T01.Majority

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The two geometric feature types in the archived field packets. -/
inductive WeightedTarget where
  | point (p : QPoint)
  | majority (sites : Finset QPoint) (threshold : ℕ)

def WeightedTarget.Valid : WeightedTarget → Prop
  | .point _ => True
  | .majority sites k => sites.card + 1 = 2 * k

instance weightedTargetValidDecidable (f : WeightedTarget) : Decidable f.Valid := by
  cases f <;> dsimp [WeightedTarget.Valid] <;> infer_instance

def WeightedTarget.Capture (f : WeightedTarget) (q : UnitSquare) : Prop :=
  match f with
  | .point p => OpenSquare q (realPoint p)
  | .majority sites k => BaselineMajorityCapture sites k q

structure WeightedFeature where
  target : WeightedTarget
  weight : ℕ

def WeightedFeature.Valid (f : WeightedFeature) : Prop := f.target.Valid

instance weightedFeatureValidDecidable (f : WeightedFeature) : Decidable f.Valid := by
  unfold WeightedFeature.Valid
  infer_instance

def WeightedFeature.Capture (f : WeightedFeature) (q : UnitSquare) : Prop :=
  f.target.Capture q

theorem weighted_feature_unique {S : ℝ} (P : Packing 11 S)
    (f : WeightedFeature) (hf : f.Valid) (i j : Owner)
    (hi : f.Capture (P.squares i)) (hj : f.Capture (P.squares j)) : i = j := by
  cases htarget : f.target with
  | point p =>
    simp only [WeightedFeature.Capture, WeightedTarget.Capture, htarget] at hi hj
    by_contra hij
    exact P.interior_disjoint i j hij (realPoint p) ⟨hi, hj⟩
  | majority sites k =>
    simp only [WeightedFeature.Valid, WeightedTarget.Valid, htarget] at hf
    simp only [WeightedFeature.Capture, WeightedTarget.Capture, htarget] at hi hj
    exact baseline_majority_unique_owner P sites k hf i j hi hj

/-- The contribution of one feature to one square. -/
def featureCharge (f : WeightedFeature) (q : UnitSquare) : ℕ := by
  classical
  exact if f.Capture q then f.weight else 0

/-- The charge earned by one square from all packet features. -/
def weightedCharge {n : ℕ} (features : Fin n → WeightedFeature)
    (q : UnitSquare) : ℕ :=
  ∑ f : Fin n, featureCharge (features f) q

def weightedBudget {n : ℕ} (features : Fin n → WeightedFeature) : ℕ :=
  ∑ f : Fin n, (features f).weight

private theorem one_feature_capacity {S : ℝ} (P : Packing 11 S)
    (f : WeightedFeature) (hf : f.Valid) (owners : Finset Owner) :
    (∑ i ∈ owners, featureCharge f (P.squares i)) ≤
      f.weight := by
  classical
  by_cases h : ∃ i ∈ owners, f.Capture (P.squares i)
  · obtain ⟨i, hi, hcap⟩ := h
    have heq : (∑ j ∈ owners, featureCharge f (P.squares j)) = f.weight := by
      calc
        (∑ j ∈ owners, featureCharge f (P.squares j)) =
            featureCharge f (P.squares i) := by
          apply Finset.sum_eq_single i
          · intro j hj hji
            have hn : ¬ f.Capture (P.squares j) := by
              intro hcapj
              exact hji (weighted_feature_unique P f hf j i hcapj hcap)
            simp [featureCharge, hn]
          · simp [hi]
        _ = f.weight := by simp [featureCharge, hcap]
    exact heq.le
  · have hz :
        (∑ i ∈ owners, featureCharge f (P.squares i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [featureCharge, show ¬ f.Capture (P.squares i) from
        fun hc => h ⟨i, hi, hc⟩]
    rw [hz]
    exact Nat.zero_le _

/-- No packing can earn more weighted feature charge than the packet budget. -/
theorem weighted_capacity {S : ℝ} (P : Packing 11 S)
    {n : ℕ} (features : Fin n → WeightedFeature)
    (hvalid : ∀ f, (features f).Valid) (owners : Finset Owner) :
    (∑ i ∈ owners, weightedCharge features (P.squares i)) ≤
      weightedBudget features := by
  classical
  unfold weightedBudget weightedCharge
  calc
    (∑ i ∈ owners, ∑ f : Fin n,
        featureCharge (features f) (P.squares i)) =
      ∑ f : Fin n, ∑ i ∈ owners,
        featureCharge (features f) (P.squares i) := by
          rw [Finset.sum_comm]
    _ ≤ ∑ f : Fin n, (features f).weight := by
      apply Finset.sum_le_sum
      intro f _
      exact one_feature_capacity P (features f) (hvalid f) owners

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.weighted_capacity
