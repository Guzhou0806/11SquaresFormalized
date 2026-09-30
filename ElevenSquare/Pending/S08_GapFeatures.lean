import ElevenSquare.Pending.S08_GapCorners
import ElevenSquare.Pending.S08_SATNecessity

namespace ElevenSquare.Pending
noncomputable section

/-- Convert an actual edge-normal halfplane bound to the archive's feature flags. -/
theorem feature_from_normal (S : ℝ) (q₀ : Owner → UnitSquare) (h : Displacement)
    (P : Packing 11 S)
    (hP : ∀ i, (P.squares i).center = perturbedCenter q₀ h i ∧
      (P.squares i).axis = perturbedAxis q₀ h i)
    (i j : Owner) (hij : i ≠ j) (n : Point)
    (hn : SeparationGeometry.EdgeNormal (P.squares i) n)
    (hb : ∀ p, ClosedSquare (P.squares j) p →
      1/2 ≤ dot (p-(P.squares i).center) n) :
    ∃ f : SeparationFeature, f.owner = i ∧ f.other = j ∧
      ∀ v : Fin 4, 0 ≤ featureGap q₀ f v h  := by
  obtain ⟨perpendicular, reverse, hgap⟩ :=
    SeparationGeometry.halfplane_feature_flags (P.squares i) (P.squares j) n hn hb
  let f : SeparationFeature := ⟨i, j, hij, perpendicular, reverse⟩
  refine ⟨f, rfl, rfl, ?_⟩
  intro v
  have hp := hgap (perturbedCorner q₀ h j v)
    (perturbedCorner_closed q₀ h j (P.squares j) (hP j).1 (hP j).2 v)
  rw [(hP i).1, (hP i).2] at hp
  exact hp

theorem feasible_pair_feature (S : ℝ) (q₀ : Owner → UnitSquare) (h : Displacement)
    (hf : LocalFeasible S q₀ h) (i j : Owner) (hij : i ≠ j) :
    ∃ f : SeparationFeature,
      ((f.owner = i ∧ f.other = j) ∨ (f.owner = j ∧ f.other = i)) ∧
      ∀ v : Fin 4, 0 ≤ featureGap q₀ f v h := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨n, hn, hsep⟩ := separating_axis_necessary (P.squares i) (P.squares j)
    (P.interior_disjoint i j hij)
  rcases SeparationGeometry.separator_owner (P.squares i) (P.squares j) n hn hsep with
    ⟨v, hv, hb⟩ | ⟨v, hv, hb⟩
  · obtain ⟨f, hi, hj, hf⟩ := feature_from_normal S q₀ h P hP i j hij v hv hb
    exact ⟨f, Or.inl ⟨hi, hj⟩, hf⟩
  · obtain ⟨f, hj, hi, hf⟩ := feature_from_normal S q₀ h P hP j i (Ne.symm hij) v hv hb
    exact ⟨f, Or.inr ⟨hj, hi⟩, hf⟩

#print axioms feature_from_normal
#print axioms feasible_pair_feature

end
end ElevenSquare.Pending
