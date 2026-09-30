import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianGuardedCertificate
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianTargetCertificate

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A finite direction witness may use an unconditional or a guarded median
order certificate. The target polygon and interval are shared. -/
inductive MedianFacetProofRef where
  | plain (certificate : MedianFacetCertificate)
  | guarded (certificate : GuardedMedianFacetCertificate)

def MedianFacetProofRef.direction : MedianFacetProofRef → MedianDirection
  | .plain c => c.direction
  | .guarded c => c.base.direction

def MedianFacetProofRef.Check (ref : MedianFacetProofRef)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half : ℚ) (guard : SymbolicQuadratic) (l u : ℚ) : Prop :=
  match ref with
  | .plain c => c.Check sites k target half l u
  | .guarded c => c.Check sites k target half guard l u

instance medianFacetProofRefCheckDecidable (ref : MedianFacetProofRef)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half : ℚ) (guard : SymbolicQuadratic) (l u : ℚ) :
    Decidable (ref.Check sites k target half guard l u) := by
  cases ref <;> dsimp [MedianFacetProofRef.Check] <;> infer_instance

theorem median_facet_proof_ref_sound (ref : MedianFacetProofRef)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half l u : ℚ) (guard : SymbolicQuadratic)
    (hc : ref.Check sites k target half guard l u)
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (hguard : 0 ≤ guard.eval t) :
    SymbolicMedianFacetWitness sites k q t half
      (ref.direction.localNormal q) target := by
  cases ref with
  | plain c =>
      exact median_facet_certificate_sound c sites k target half l u
        hc q t ha hlt htu
  | guarded c =>
      exact guarded_median_facet_certificate_sound c sites k target
        half l u guard hc q t ha hlt htu hguard

/-- Finite mixed roster: all ordinary signs remain reusable while only the
switching directions pay for guarded polynomial checks. -/
structure MixedMedianTargetCertificate where
  pairs : Finset (QPoint × QPoint)
  facets : List MedianFacetProofRef

def MixedMedianTargetCertificate.Check (C : MixedMedianTargetCertificate)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half : ℚ) (guard : SymbolicQuadratic) (l u : ℚ) : Prop :=
  (∀ ref ∈ C.facets, ref.Check sites k target half guard l u) ∧
  (∀ d ∈ medianAxisDirections, ∃ ref ∈ C.facets, ref.direction = d) ∧
  (∀ ab ∈ C.pairs, ∀ negative : Bool,
    ∃ ref ∈ C.facets, ref.direction = .pair ab.1 ab.2 negative) ∧
  (∀ a ∈ sites, ∀ b ∈ sites, a ≠ b →
    (a,b) ∈ C.pairs ∨ (b,a) ∈ C.pairs)

instance mixedMedianTargetCertificateCheckDecidable
    (C : MixedMedianTargetCertificate) (sites : Finset QPoint) (k : ℕ)
    (target : List SymbolicFacet) (half : ℚ)
    (guard : SymbolicQuadratic) (l u : ℚ) :
    Decidable (C.Check sites k target half guard l u) := by
  unfold MixedMedianTargetCertificate.Check
  infer_instance

theorem mixed_median_target_certificate_sound (C : MixedMedianTargetCertificate)
    (sites : Finset QPoint) (k : ℕ) (target : List SymbolicFacet)
    (half l u : ℚ) (guard : SymbolicQuadratic)
    (hC : C.Check sites k target half guard l u)
    (q : UnitSquare) (t : ℝ) (ha : q.axis = chartAxis t)
    (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (hguard : 0 ≤ guard.eval t)
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
      have hw := median_facet_proof_ref_sound c sites k target half l u guard
        (hfacets c hcmem) q t ha hlt htu hguard
      simpa [hcdir, MedianDirection.localNormal] using hw
    · subst axis
      rcases haxes .uNeg (by simp [medianAxisDirections]) with ⟨c, hcmem, hcdir⟩
      have hw := median_facet_proof_ref_sound c sites k target half l u guard
        (hfacets c hcmem) q t ha hlt htu hguard
      simpa [hcdir, MedianDirection.localNormal] using hw
    · subst axis
      rcases haxes .vPos (by simp [medianAxisDirections]) with ⟨c, hcmem, hcdir⟩
      have hw := median_facet_proof_ref_sound c sites k target half l u guard
        (hfacets c hcmem) q t ha hlt htu hguard
      simpa [hcdir, MedianDirection.localNormal] using hw
    · subst axis
      rcases haxes .vNeg (by simp [medianAxisDirections]) with ⟨c, hcmem, hcdir⟩
      have hw := median_facet_proof_ref_sound c sites k target half l u guard
        (hfacets c hcmem) q t ha hlt htu hguard
      simpa [hcdir, MedianDirection.localNormal] using hw
  · intro ab hab
    rcases hpairs ab hab false with ⟨cf, hcf, hdf⟩
    rcases hpairs ab hab true with ⟨ct, hct, hdt⟩
    have hwf := median_facet_proof_ref_sound cf sites k target half l u guard
      (hfacets cf hcf) q t ha hlt htu hguard
    have hwt := median_facet_proof_ref_sound ct sites k target half l u guard
      (hfacets ct hct) q t ha hlt htu hguard
    rw [hdf] at hwf
    rw [hdt] at hwt
    exact ⟨hwf, hwt⟩

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.median_facet_proof_ref_sound
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.mixed_median_target_certificate_sound
