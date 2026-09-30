import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCachedFarkas

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- A sign-reference list checks the original target facets and original
Farkas witnesses in order. No geometric witness is copied into the cache. -/
def CachedPolygonSignRefs.Check
    (cache : List CachedQuarticSign) (source : List SymbolicFacet)
    (l u : ℚ) : List SymbolicFacet → List SymbolicFarkasWitness →
      List CachedFarkasSigns → Prop
  | [], [], [] => True
  | target :: targets, w :: ws, signs :: rest =>
      signs.Check cache w source target l u ∧
        CachedPolygonSignRefs.Check cache source l u targets ws rest
  | _, _, _ => False

instance cachedPolygonSignRefsCheckDecidable
    (cache : List CachedQuarticSign) (source : List SymbolicFacet)
    (l u : ℚ) (targets : List SymbolicFacet)
    (ws : List SymbolicFarkasWitness) (signs : List CachedFarkasSigns) :
    Decidable (CachedPolygonSignRefs.Check cache source l u targets ws signs) := by
  induction targets generalizing ws signs with
  | nil =>
      cases ws <;> cases signs <;>
        first
        | exact inferInstanceAs (Decidable True)
        | exact inferInstanceAs (Decidable False)
  | cons target targets ih =>
      cases ws with
      | nil =>
          cases signs <;> exact inferInstanceAs (Decidable False)
      | cons w ws =>
          cases signs with
          | nil => exact inferInstanceAs (Decidable False)
          | cons s rest =>
              change Decidable (s.Check cache w source target l u ∧
                CachedPolygonSignRefs.Check cache source l u targets ws rest)
              letI := ih ws rest
              infer_instance

theorem cached_polygon_sign_refs_sound
    (cache : List CachedQuarticSign) (hcache : SymbolicSignCache.Check cache)
    (source targets : List SymbolicFacet)
    (ws : List SymbolicFarkasWitness) (signs : List CachedFarkasSigns)
    (l u : ℚ)
    (hc : CachedPolygonSignRefs.Check cache source l u targets ws signs)
    (t : ℝ) (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (x : Point) (hx : SymbolicPolygonContains source t x) :
    SymbolicPolygonContains targets t x := by
  induction targets generalizing ws signs with
  | nil =>
      intro target hmem
      simp at hmem
  | cons target targets ih =>
      cases ws with
      | nil => cases signs <;> cases hc
      | cons w ws =>
          cases signs with
          | nil => cases hc
          | cons s rest =>
              rcases hc with ⟨hhead, htail⟩
              intro desired hmem
              rcases List.mem_cons.mp hmem with hfirst | hrest
              · subst desired
                exact cached_farkas_sound s cache hcache w source target
                  l u hhead t hlt htu x hx
              · exact ih ws rest htail desired hrest

/-- The raw moving BSP and every raw Farkas witness are reused unchanged.
This parallel tree carries only four sign-cache references per implication. -/
inductive SymbolicCoverSignRefs where
  | hit (signs : List CachedFarkasSigns)
  | split (left right : SymbolicCoverSignRefs)

def SymbolicCoverSignRefs.Check
    (cache : List CachedQuarticSign) (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (l u : ℚ) :
    SymbolicCoverCertificate → SymbolicCoverSignRefs → Prop
  | .hit index ws, .hit signs =>
      index < targets.length ∧
        CachedPolygonSignRefs.Check cache source l u
          (targets.getD index []) ws signs
  | .split facet left right, .split signLeft signRight =>
      SymbolicCoverSignRefs.Check cache (facet :: source) targets l u
        left signLeft ∧
      SymbolicCoverSignRefs.Check cache (facet.flip :: source) targets l u
        right signRight
  | _, _ => False

instance symbolicCoverSignRefsCheckDecidable
    (cache : List CachedQuarticSign) (source : List SymbolicFacet)
    (targets : List (List SymbolicFacet)) (l u : ℚ)
    (cover : SymbolicCoverCertificate) (signs : SymbolicCoverSignRefs) :
    Decidable (SymbolicCoverSignRefs.Check cache source targets l u cover signs) := by
  induction cover generalizing source signs with
  | hit index ws =>
      cases signs with
      | hit ss =>
          change Decidable (index < targets.length ∧
            CachedPolygonSignRefs.Check cache source l u
              (targets.getD index []) ws ss)
          infer_instance
      | split left right => exact inferInstanceAs (Decidable False)
  | split facet left right ihl ihr =>
      cases signs with
      | hit ss => exact inferInstanceAs (Decidable False)
      | split signLeft signRight =>
          change Decidable
            (SymbolicCoverSignRefs.Check cache (facet :: source) targets l u
              left signLeft ∧
             SymbolicCoverSignRefs.Check cache (facet.flip :: source) targets l u
              right signRight)
          letI := ihl (facet :: source) signLeft
          letI := ihr (facet.flip :: source) signRight
          infer_instance

theorem symbolic_cached_cover_sound
    (cache : List CachedQuarticSign) (hcache : SymbolicSignCache.Check cache)
    (source : List SymbolicFacet) (targets : List (List SymbolicFacet))
    (l u : ℚ) (cover : SymbolicCoverCertificate)
    (signs : SymbolicCoverSignRefs)
    (hc : SymbolicCoverSignRefs.Check cache source targets l u cover signs)
    (t : ℝ) (hlt : (l : ℝ) ≤ t) (htu : t ≤ (u : ℝ))
    (x : Point) (hx : SymbolicPolygonContains source t x) :
    ∃ target ∈ targets, SymbolicPolygonContains target t x := by
  induction cover generalizing source signs with
  | hit index ws =>
      cases signs with
      | hit ss =>
          refine ⟨targets.getD index [], ?_, ?_⟩
          · rw [List.getD_eq_get targets [] hc.1]
            exact List.get_mem ..
          · exact cached_polygon_sign_refs_sound cache hcache source
              (targets.getD index []) ws ss l u hc.2 t hlt htu x hx
      | split signLeft signRight => cases hc
  | split facet left right ihl ihr =>
      cases signs with
      | hit ss => cases hc
      | split signLeft signRight =>
          by_cases hfacet : facet.contains t x
          · apply ihl (facet :: source) signLeft hc.1
            intro f hf
            rcases List.mem_cons.mp hf with rfl | hf
            · exact hfacet
            · exact hx f hf
          · apply ihr (facet.flip :: source) signRight hc.2
            intro f hf
            rcases List.mem_cons.mp hf with rfl | hf
            · exact symbolic_facet_flip_contains facet t x hfacet
            · exact hx f hf

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.symbolic_cached_cover_sound
