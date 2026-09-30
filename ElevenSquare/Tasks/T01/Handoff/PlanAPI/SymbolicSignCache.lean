import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicGuardedCover
import ElevenSquare.Tasks.T01.QuarticScale

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01
noncomputable section

/-- One raw exact interval sign certificate, reusable by every symbolic row
whose angle interval lies inside this certificate's interval. -/
structure CachedQuarticSign where
  polynomial : Quartic
  lower : ℚ
  upper : ℚ
  strict : Bool
  intervalCertificate : QuarticIntervalCertificate

def CachedQuarticSign.Check (entry : CachedQuarticSign) : Prop :=
  entry.intervalCertificate.Check entry.strict entry.polynomial
    entry.lower entry.upper

instance cachedQuarticSignCheckDecidable (entry : CachedQuarticSign) :
    Decidable entry.Check := by
  unfold CachedQuarticSign.Check
  infer_instance

def SymbolicSignCache.Check : List CachedQuarticSign → Prop
  | [] => True
  | entry :: rest => entry.Check ∧ SymbolicSignCache.Check rest

instance symbolicSignCacheCheckDecidable (cache : List CachedQuarticSign) :
    Decidable (SymbolicSignCache.Check cache) := by
  induction cache with
  | nil => exact inferInstanceAs (Decidable True)
  | cons entry rest ih =>
      change Decidable (entry.Check ∧ SymbolicSignCache.Check rest)
      infer_instance

theorem symbolic_sign_cache_entry_checked (cache : List CachedQuarticSign)
    (hc : SymbolicSignCache.Check cache)
    (entry : CachedQuarticSign) (hmem : entry ∈ cache) :
    entry.Check := by
  induction cache with
  | nil => simp at hmem
  | cons head tail ih =>
      rcases hc with ⟨hhead, htail⟩
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hhead
      · exact ih htail hmem

theorem cached_quartic_sign_sound (entry : CachedQuarticSign)
    (hc : entry.Check) (t : ℝ)
    (hlt : (entry.lower : ℝ) ≤ t) (htu : t ≤ (entry.upper : ℝ)) :
    if entry.strict then 0 < entry.polynomial.eval t
      else 0 ≤ entry.polynomial.eval t :=
  quartic_interval_certificate_sound entry.strict entry.polynomial
    entry.lower entry.upper entry.intervalCertificate hc t hlt htu

private def defaultCachedQuarticSign : CachedQuarticSign :=
  ⟨⟨0, 0, 0, 0, 0⟩, 0, 1, false, .leaf⟩

/-- A checked reference into a reusable sign cache. The local row interval,
polynomial and strictness are all compared as exact rational data. -/
structure QuarticSignRef where
  index : ℕ
  scale : ℚ
  deriving DecidableEq

def QuarticSignRef.entry (ref : QuarticSignRef)
    (cache : List CachedQuarticSign) : CachedQuarticSign :=
  cache.getD ref.index defaultCachedQuarticSign

def QuarticSignRef.Check (ref : QuarticSignRef)
    (cache : List CachedQuarticSign) (polynomial : Quartic)
    (strict : Bool) (lower upper : ℚ) : Prop :=
  ref.index < cache.length ∧
    let entry := ref.entry cache
    0 < ref.scale ∧ polynomial = entry.polynomial.scale ref.scale ∧
      (strict = true → entry.strict = true) ∧
      entry.lower ≤ lower ∧ upper ≤ entry.upper

instance quarticSignRefCheckDecidable (ref : QuarticSignRef)
    (cache : List CachedQuarticSign) (polynomial : Quartic)
    (strict : Bool) (lower upper : ℚ) :
    Decidable (ref.Check cache polynomial strict lower upper) := by
  unfold QuarticSignRef.Check
  infer_instance

theorem quartic_sign_ref_sound (ref : QuarticSignRef)
    (cache : List CachedQuarticSign) (hc : SymbolicSignCache.Check cache)
    (polynomial : Quartic) (strict : Bool) (lower upper : ℚ)
    (hr : ref.Check cache polynomial strict lower upper)
    (t : ℝ) (hlt : (lower : ℝ) ≤ t) (htu : t ≤ (upper : ℝ)) :
    if strict then 0 < polynomial.eval t else 0 ≤ polynomial.eval t := by
  rcases hr with ⟨hindex, hscale, hpoly, hstrict, hlower, hupper⟩
  have hmem : ref.entry cache ∈ cache := by
    unfold QuarticSignRef.entry
    rw [List.getD_eq_get cache defaultCachedQuarticSign hindex]
    exact List.get_mem ..
  have hentry := symbolic_sign_cache_entry_checked cache hc
    (ref.entry cache) hmem
  have hboundL : ((ref.entry cache).lower : ℝ) ≤ t := by
    have hcast : ((ref.entry cache).lower : ℝ) ≤ (lower : ℝ) :=
      by exact_mod_cast hlower
    exact le_trans hcast hlt
  have hboundU : t ≤ ((ref.entry cache).upper : ℝ) := by
    have hcast : (upper : ℝ) ≤ ((ref.entry cache).upper : ℝ) :=
      by exact_mod_cast hupper
    exact le_trans htu hcast
  have hsound := cached_quartic_sign_sound (ref.entry cache) hentry
    t hboundL hboundU
  have hs : 0 < (ref.scale : ℝ) := by exact_mod_cast hscale
  cases strict with
  | false =>
      simp only [↓reduceIte]
      rw [hpoly, quartic_scale_eval]
      cases hentryStrict : (ref.entry cache).strict with
      | false =>
          simp only [hentryStrict, ↓reduceIte] at hsound
          exact mul_nonneg hs.le hsound
      | true =>
          simp only [hentryStrict, ↓reduceIte] at hsound
          exact (mul_pos hs hsound).le
  | true =>
      have hentryStrict : (ref.entry cache).strict = true := hstrict rfl
      simp only [hentryStrict, ↓reduceIte] at hsound
      simp only [↓reduceIte]
      rw [hpoly, quartic_scale_eval]
      exact mul_pos hs hsound

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.quartic_sign_ref_sound
