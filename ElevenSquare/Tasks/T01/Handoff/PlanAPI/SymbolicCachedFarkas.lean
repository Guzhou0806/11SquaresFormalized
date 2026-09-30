import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicSignCache

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Only sign references are added to the original exact Farkas witness.
Its source indices, dual coefficients and normal identities are unchanged. -/
structure CachedFarkasSigns where
  denominator : QuarticSignRef
  firstWeight : QuarticSignRef
  secondWeight : QuarticSignRef
  margin : QuarticSignRef

def CachedFarkasSigns.Check (signs : CachedFarkasSigns)
    (cache : List CachedQuarticSign) (w : SymbolicFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet)
    (l u : ℚ) : Prop :=
  w.first < source.length ∧ w.second < source.length ∧
  let zero : SymbolicFacet := ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩
  let f := source.getD w.first zero
  let g := source.getD w.second zero
  signs.denominator.Check cache w.denominator.quartic true l u ∧
  signs.firstWeight.Check cache w.firstWeight.quartic false l u ∧
  signs.secondWeight.Check cache w.secondWeight.quartic false l u ∧
  quarticAdd (w.firstWeight.mul f.a) (w.secondWeight.mul g.a) =
    w.denominator.mul target.a ∧
  quarticAdd (w.firstWeight.mul f.b) (w.secondWeight.mul g.b) =
    w.denominator.mul target.b ∧
  signs.margin.Check cache (w.margin f g target) false l u

instance cachedFarkasSignsCheckDecidable (signs : CachedFarkasSigns)
    (cache : List CachedQuarticSign) (w : SymbolicFarkasWitness)
    (source : List SymbolicFacet) (target : SymbolicFacet)
    (l u : ℚ) : Decidable (signs.Check cache w source target l u) := by
  unfold CachedFarkasSigns.Check
  infer_instance

theorem cached_farkas_sound (signs : CachedFarkasSigns)
    (cache : List CachedQuarticSign) (hcache : SymbolicSignCache.Check cache)
    (w : SymbolicFarkasWitness) (source : List SymbolicFacet)
    (target : SymbolicFacet) (l u : ℚ)
    (hc : signs.Check cache w source target l u)
    (t : ℝ) (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (x : Point) (hx : SymbolicPolygonContains source t x) :
    target.contains t x := by
  rcases hc with ⟨hfirst, hsecond, hden, hweight1,
    hweight2, ha, hb, hmargin⟩
  apply symbolic_farkas_pointwise w source target hfirst hsecond ha hb
    t x hx
  · have hp := quartic_sign_ref_sound signs.denominator cache hcache
      w.denominator.quartic true l u hden t hlt htu
    change 0 < w.denominator.quartic.eval t at hp
    simpa only [symbolic_quadratic_quartic_eval] using hp
  · have hp := quartic_sign_ref_sound signs.firstWeight cache hcache
      w.firstWeight.quartic false l u hweight1 t hlt htu
    change 0 ≤ w.firstWeight.quartic.eval t at hp
    simpa only [symbolic_quadratic_quartic_eval] using hp
  · have hp := quartic_sign_ref_sound signs.secondWeight cache hcache
      w.secondWeight.quartic false l u hweight2 t hlt htu
    change 0 ≤ w.secondWeight.quartic.eval t at hp
    simpa only [symbolic_quadratic_quartic_eval] using hp
  · exact quartic_sign_ref_sound signs.margin cache hcache
      (w.margin
        (source.getD w.first ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩)
        (source.getD w.second ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩⟩)
        target) false l u hmargin t hlt htu

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.cached_farkas_sound
