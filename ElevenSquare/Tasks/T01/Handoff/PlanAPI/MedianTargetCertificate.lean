import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianFiniteCertificate

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The four local coordinate directions. -/
def medianAxisDirections : List MedianDirection :=
  [.uPos, .uNeg, .vPos, .vNeg]

/-- Finite data identifying the 24 support directions needed for a five-site
median target: four axes and both signs of every selected site pair. -/
structure MedianTargetCertificate where
  pairs : Finset (QPoint × QPoint)
  facets : List MedianFacetCertificate

def MedianTargetCertificate.Check (C : MedianTargetCertificate)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half l u : ℚ) : Prop :=
  (∀ c ∈ C.facets, c.Check sites k target half l u) ∧
  (∀ d ∈ medianAxisDirections, ∃ c ∈ C.facets, c.direction = d) ∧
  (∀ ab ∈ C.pairs, ∀ negative : Bool,
    ∃ c ∈ C.facets, c.direction = .pair ab.1 ab.2 negative) ∧
  (∀ a ∈ sites, ∀ b ∈ sites, a ≠ b →
    (a,b) ∈ C.pairs ∨ (b,a) ∈ C.pairs)

theorem median_target_certificate_sound (C : MedianTargetCertificate)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half l u : ℚ) (hC : C.Check sites k target half l u)
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (hwidth : 0 ≤ (half : ℝ) ∧ (half : ℝ) < 1 / 2)
    (hk : 0 < k)
    (hcontains : SymbolicPolygonContains target t q.center) :
    BaselineMajorityCapture sites k q := by
  rcases hC with ⟨hfacets, haxes, hpairs, hcover⟩
  apply symbolic_majority_of_pair_cover sites C.pairs k q t half
    hwidth hk ha target hcontains hcover
  · intro axis haxis
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at haxis
    rcases haxis with haxis | haxis | haxis | haxis
    · subst axis
      rcases haxes .uPos (by simp [medianAxisDirections]) with ⟨c, hcmem, hcdir⟩
      have hw := median_facet_certificate_sound c sites k target half l u
        (hfacets c hcmem) q t ha hlt htu
      simpa [hcdir, MedianDirection.localNormal] using hw
    · subst axis
      rcases haxes .uNeg (by simp [medianAxisDirections]) with ⟨c, hcmem, hcdir⟩
      have hw := median_facet_certificate_sound c sites k target half l u
        (hfacets c hcmem) q t ha hlt htu
      simpa [hcdir, MedianDirection.localNormal] using hw
    · subst axis
      rcases haxes .vPos (by simp [medianAxisDirections]) with ⟨c, hcmem, hcdir⟩
      have hw := median_facet_certificate_sound c sites k target half l u
        (hfacets c hcmem) q t ha hlt htu
      simpa [hcdir, MedianDirection.localNormal] using hw
    · subst axis
      rcases haxes .vNeg (by simp [medianAxisDirections]) with ⟨c, hcmem, hcdir⟩
      have hw := median_facet_certificate_sound c sites k target half l u
        (hfacets c hcmem) q t ha hlt htu
      simpa [hcdir, MedianDirection.localNormal] using hw
  · intro ab hab
    rcases hpairs ab hab false with ⟨cf, hcf, hdf⟩
    rcases hpairs ab hab true with ⟨ct, hct, hdt⟩
    have hwf := median_facet_certificate_sound cf sites k target half l u
      (hfacets cf hcf) q t ha hlt htu
    have hwt := median_facet_certificate_sound ct sites k target half l u
      (hfacets ct hct) q t ha hlt htu
    rw [hdf] at hwf
    rw [hdt] at hwt
    exact ⟨hwf, hwt⟩

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.median_target_certificate_sound
