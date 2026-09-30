import ElevenSquare.Pending.S08_Packet
import ElevenSquare.Pending.S08_DualEstimate
import ElevenSquare.Pending.S08_Taylor

/-! Local isolation from branch, Taylor, and exact dual certificate predicates. -/

namespace ElevenSquare.Pending
noncomputable section

-- The main analytic theorem. The rectangle is closed and angular coordinates are radians.
theorem packet_isolates (S : ℝ) (q₀ : Owner → UnitSquare) (p : LocalPacket)
    (hbranches : BranchCover S q₀ p) (htied : RowsTied S q₀ p)
    (htaylor : RowsTaylorBound S q₀ p) (hdual : DualBounds S q₀ p) :
    ∀ h, InRectangle p.radii h → LocalFeasible S q₀ h → h = 0 := by
  intro h hrect hfeasible
  by_contra hn
  rcases hdual with ⟨hr, hR, hK, hw, heps, hres, hstrict⟩
  obtain ⟨τ, hτpos, hτle, hbox, j, hj⟩ :=
    normalized_radius_attained p.radii h (fun k => (hr k).1) hrect hn
  let u : Displacement := fun k => h k / τ
  have hτne : τ ≠ 0 := ne_of_gt hτpos
  have hurect : InRectangle p.radii u := by
    intro k
    dsimp [u]
    rw [abs_div, abs_of_pos hτpos]
    apply (div_le_iff hτpos).mpr
    simpa only [mul_comm] using hbox k
  have hscale : τ • u = h := by
    funext k
    dsimp [u]
    field_simp
  have linear_scale (a : Fin 33 → ℝ) : τ*LinearForm a u = LinearForm a h := by
    unfold LinearForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [u]
    field_simp
  obtain ⟨b, hb⟩ := hbranches h hrect hfeasible
  have hrows (i : Fin 42) : -(τ^2*(p.curvature b i : ℝ)/2) ≤
      LinearForm (gapGradient S q₀ (p.representative b i)) h := by
    obtain ⟨g, hg, hgf⟩ := hb i
    have hzero := ((htied b i).2 g hg).1
    have herr := htaylor b i g hg u hurect τ ⟨hτpos.le, hτle⟩
    rw [hscale, linear_scale] at herr
    exact tied_gap_linear_lower (gapValue S q₀ g)
      (gapGradient S q₀ (p.representative b i)) h τ (p.curvature b i : ℝ)
      hzero hgf herr
  have hsign : ∃ s : Fin 2, -(dualSign s*h j) = |h j| := by
    by_cases hjpos : 0 ≤ h j
    · refine ⟨0, ?_⟩
      simp [dualSign, abs_of_nonneg hjpos]
    · refine ⟨1, ?_⟩
      simp [dualSign, abs_of_neg (lt_of_not_ge hjpos)]
  obtain ⟨s, hs⟩ := hsign
  have hweights (i : Fin 42) : 0 ≤ (p.dual b j s i : ℝ) := by
    exact_mod_cast hw b j s i
  have hcurv (i : Fin 42) : 0 ≤ (p.curvature b i : ℝ) := by
    exact_mod_cast hK b i
  have hε : 0 ≤ (p.residual b j s : ℝ) := by exact_mod_cast heps b j s
  have hbound := dual_signed_coordinate_bound
    (fun i => gapGradient S q₀ (p.representative b i))
    (fun i => (p.dual b j s i : ℝ)) (fun i => (p.curvature b i : ℝ))
    h j (dualSign s) (p.residual b j s : ℝ) τ p.maxRadius
    hweights hε hτpos.le hR
    (fun k => (hbox k).trans (mul_le_mul_of_nonneg_left (hr k).2.1 hτpos.le))
    hrows (hres b j s)
  rw [hs, hj] at hbound
  exact strict_dual_contradiction τ (p.radii j) (p.residual b j s : ℝ) p.maxRadius
    (∑ i, (p.dual b j s i : ℝ)*(p.curvature b i : ℝ))
    ⟨hτpos, hτle⟩ (hr j).1 hε hR
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hweights i) (hcurv i)))
    (hstrict b j s) hbound


end
end ElevenSquare.Pending
