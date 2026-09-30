import ElevenSquare.Pending.S08_Packet
import ElevenSquare.Pending.S08_Taylor

/-! Finite branch selection from complete feature-choice and wall premises. -/

namespace ElevenSquare.Pending
noncomputable section

-- A negative selected corner rules out the WHOLE separation feature.
theorem unavailable_feature_excluded (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (h : Displacement) (hneg : featureGap q₀ f v h < 0) :
    ¬ ∀ w : Fin 4, 0 ≤ featureGap q₀ f w h := by
  intro hnonneg
  exact (not_lt_of_ge (hnonneg v)) hneg

-- Pure finite selection step, independently reusable once the actual 14-pair
-- and 128-branch inventories and aliases have been proved complete.
theorem branch_cover_from_feature_choices
    (S : ℝ) (q₀ : Owner → UnitSquare) (p : LocalPacket)
    (features : Fin 14 → List SeparationFeature)
    (hchoices : ∀ h, InRectangle p.radii h → LocalFeasible S q₀ h →
      ∀ pair, ∃ f ∈ features pair, ∀ v, 0 ≤ featureGap q₀ f v h)
    (hbranch : ∀ choose : Fin 14 → SeparationFeature,
      (∀ pair, choose pair ∈ features pair) →
      ∃ b : Fin 128, ∀ h,
        (∀ pair v, 0 ≤ featureGap q₀ (choose pair) v h) →
        (∀ i v w, 0 ≤ gapValue S q₀ (.wall i v w) h) →
        ∀ row, ∃ g ∈ p.aliases b row, 0 ≤ gapValue S q₀ g h) :
    BranchCover S q₀ p := by
  classical
  intro h hrect hf
  have hc := hchoices h hrect hf
  choose choose hmem hnonneg using hc
  obtain ⟨b, hb⟩ := hbranch choose hmem
  exact ⟨b, hb h hnonneg (fun i v w => feasible_wall_gaps S q₀ h hf i v w)⟩


end
end ElevenSquare.Pending
