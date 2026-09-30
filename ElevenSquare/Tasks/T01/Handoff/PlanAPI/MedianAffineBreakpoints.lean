import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianFiniteNormal
import Mathlib.Topology.Order.IntermediateValue

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

/-- An affine support value on one quadrant of the L1 unit circle. -/
def affineValue (line : ℝ × ℝ) (t : ℝ) : ℝ := line.1 * t + line.2

/-- A bound between two affine functions interpolates from the endpoints. -/
theorem affine_support_interpolate (source target : ℝ × ℝ) (l t u : ℝ)
    (hlt : l ≤ t) (htu : t ≤ u) (hlu : l < u)
    (hl : affineValue target l ≤ affineValue source l)
    (hu : affineValue target u ≤ affineValue source u) :
    affineValue target t ≤ affineValue source t := by
  have hleft : (u - t) * (affineValue target l - affineValue source l) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr htu) (sub_nonpos.mpr hl)
  have hright : (t - l) * (affineValue target u - affineValue source u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlt) (sub_nonpos.mpr hu)
  have hid : (u - l) * (affineValue target t - affineValue source t) =
      (u - t) * (affineValue target l - affineValue source l) +
      (t - l) * (affineValue target u - affineValue source u) := by
    dsimp [affineValue]
    ring
  nlinarith

/-- The unique crossing parameter of two lines with different slopes. -/
def affineCross (p q : ℝ × ℝ) : ℝ :=
  if p.1 = q.1 then 0 else (q.2 - p.2) / (p.1 - q.1)

theorem affine_tie_eq_cross (p q : ℝ × ℝ) (t : ℝ)
    (hslope : p.1 ≠ q.1)
    (htie : affineValue p t = affineValue q t) :
    t = affineCross p q := by
  have hden : p.1 - q.1 ≠ 0 := sub_ne_zero.mpr hslope
  have heq : (p.1 - q.1) * t = q.2 - p.2 := by
    dsimp [affineValue] at htie
    linarith
  dsimp [affineCross]
  rw [if_neg hslope, eq_div_iff hden]
  nlinarith [heq]

theorem affine_tie_at_cross (p q : ℝ × ℝ)
    (hslope : p.1 ≠ q.1) :
    affineValue p (affineCross p q) =
      affineValue q (affineCross p q) := by
  have hden : p.1 - q.1 ≠ 0 := sub_ne_zero.mpr hslope
  dsimp [affineCross, affineValue]
  rw [if_neg hslope]
  field_simp [hden]
  ring

/-- A strict ordering reversal creates a crossing in the interval, including
    a possible tie at the right endpoint. -/
theorem affine_crosses_right (p q : ℝ × ℝ) (l t : ℝ)
    (hlt : l ≤ t)
    (hl : affineValue p l < affineValue q l)
    (ht : affineValue q t ≤ affineValue p t) :
    ∃ r, l < r ∧ r ≤ t ∧ p.1 ≠ q.1 ∧ r = affineCross p q := by
  have hslope : p.1 ≠ q.1 := by
    intro heq
    dsimp [affineValue] at hl ht
    rw [heq] at hl ht
    linarith
  have hcontinuous : ContinuousOn
      (fun r : ℝ => affineValue p r - affineValue q r) (Set.Icc l t) := by
    dsimp [affineValue]
    fun_prop
  have hzero : (0 : ℝ) ∈ Set.Icc
      (affineValue p l - affineValue q l)
      (affineValue p t - affineValue q t) := ⟨by linarith, by linarith⟩
  obtain ⟨r, ⟨hrlo, hrhi⟩, hrzero⟩ :=
    (intermediate_value_Icc hlt hcontinuous) hzero
  have htie : affineValue p r = affineValue q r := by
    dsimp at hrzero
    linarith
  refine ⟨r, ?_, hrhi, hslope, affine_tie_eq_cross p q r hslope htie⟩
  rcases lt_or_eq_of_le hrlo with hrlt | hreq
  · exact hrlt
  · subst r
    linarith

/-- The symmetric crossing statement, strict at the right endpoint. -/
theorem affine_crosses_left (p q : ℝ × ℝ) (t u : ℝ)
    (htu : t ≤ u)
    (ht : affineValue q t ≤ affineValue p t)
    (hu : affineValue p u < affineValue q u) :
    ∃ r, t ≤ r ∧ r < u ∧ p.1 ≠ q.1 ∧ r = affineCross p q := by
  have hslope : p.1 ≠ q.1 := by
    intro heq
    dsimp [affineValue] at ht hu
    rw [heq] at ht hu
    linarith
  have hcontinuous : ContinuousOn
      (fun r : ℝ => affineValue p r - affineValue q r) (Set.Icc t u) := by
    dsimp [affineValue]
    fun_prop
  have hzero : (0 : ℝ) ∈ Set.Icc
      (affineValue p u - affineValue q u)
      (affineValue p t - affineValue q t) := ⟨by linarith, by linarith⟩
  obtain ⟨r, ⟨hrlo, hrhi⟩, hrzero⟩ :=
    (intermediate_value_Icc' htu hcontinuous) hzero
  have htie : affineValue p r = affineValue q r := by
    dsimp at hrzero
    linarith
  refine ⟨r, hrlo, ?_, hslope, affine_tie_eq_cross p q r hslope htie⟩
  rcases lt_or_eq_of_le hrhi with hrlt | hreq
  · exact hrlt
  · subst r
    linarith

/-- Axis endpoints and all pairwise affine crossing parameters. Crossings
    outside `[0,1]` do no harm. -/
noncomputable def affineBreakpoints (lines : Finset (ℝ × ℝ)) : Finset ℝ := by
  classical
  exact insert 0 (insert 1 ((lines.product lines).image
    (fun pair => affineCross pair.1 pair.2)))

theorem affine_cross_mem_breakpoints (lines : Finset (ℝ × ℝ))
    (p q : ℝ × ℝ) (hp : p ∈ lines) (hq : q ∈ lines) :
    affineCross p q ∈ affineBreakpoints lines := by
  classical
  unfold affineBreakpoints
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  exact ⟨(p,q), Finset.mem_product.mpr ⟨hp,hq⟩, rfl⟩

theorem affineBreakpoints_mono {small large : Finset (ℝ × ℝ)}
    (hsubset : small ⊆ large) :
    affineBreakpoints small ⊆ affineBreakpoints large := by
  classical
  intro r hr
  unfold affineBreakpoints at hr ⊢
  simp only [Finset.mem_insert] at hr ⊢
  rcases hr with hr | hr | hr
  · exact Or.inl hr
  · exact Or.inr (Or.inl hr)
  · right
    right
    obtain ⟨pair, hpair, hp⟩ := Finset.mem_image.mp hr
    apply Finset.mem_image.mpr
    refine ⟨pair, ?_, hp⟩
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hpair
    exact Finset.mem_product.mpr ⟨hsubset ha, hsubset hb⟩

/-- If a target affine function lies below the finite upper envelope at the
    axes and every site-pair tie, it lies below that envelope throughout the
    quadrant. No ordering of the sites is assumed. -/
theorem finite_affine_envelope_of_breakpoints
    (lines : Finset (ℝ × ℝ)) (target : ℝ × ℝ)
    (hnonempty : lines.Nonempty)
    (hbreak : ∀ r ∈ affineBreakpoints lines, 0 ≤ r → r ≤ 1 →
      ∃ p ∈ lines, affineValue target r ≤ affineValue p r)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ p ∈ lines, affineValue target t ≤ affineValue p t := by
  classical
  let C := affineBreakpoints lines
  let L := C.filter (fun r => r ≤ t)
  let U := C.filter (fun r => t ≤ r)
  have h0C : (0 : ℝ) ∈ C := by
    dsimp [C, affineBreakpoints]
    simp
  have h1C : (1 : ℝ) ∈ C := by
    dsimp [C, affineBreakpoints]
    simp
  have h0L : (0 : ℝ) ∈ L := Finset.mem_filter.mpr ⟨h0C, ht0⟩
  have h1U : (1 : ℝ) ∈ U := Finset.mem_filter.mpr ⟨h1C, ht1⟩
  obtain ⟨l, hlL, hlmax⟩ := L.exists_max_image id ⟨0, h0L⟩
  obtain ⟨u, huU, humin⟩ := U.exists_min_image id ⟨1, h1U⟩
  have hlC : l ∈ C := (Finset.mem_filter.mp hlL).1
  have hlt : l ≤ t := (Finset.mem_filter.mp hlL).2
  have htu : t ≤ u := (Finset.mem_filter.mp huU).2
  have huC : u ∈ C := (Finset.mem_filter.mp huU).1
  have h0l : 0 ≤ l := by simpa using hlmax 0 h0L
  have hu1 : u ≤ 1 := by simpa using humin 1 h1U
  obtain ⟨p, hp, hpmax⟩ := lines.exists_max_image
    (fun s => affineValue s t) hnonempty
  have hlmax' : ∀ q ∈ lines, affineValue q l ≤ affineValue p l := by
    intro q hq
    by_contra hnot
    have hstrict : affineValue p l < affineValue q l := lt_of_not_ge hnot
    obtain ⟨r, hlr, hrt, _hslope, hcross⟩ :=
      affine_crosses_right p q l t hlt hstrict (hpmax q hq)
    have hrL : r ∈ L := Finset.mem_filter.mpr
      ⟨hcross ▸ affine_cross_mem_breakpoints lines p q hp hq, hrt⟩
    have hrle : r ≤ l := by simpa using hlmax r hrL
    exact (not_le_of_gt hlr) hrle
  have humax' : ∀ q ∈ lines, affineValue q u ≤ affineValue p u := by
    intro q hq
    by_contra hnot
    have hstrict : affineValue p u < affineValue q u := lt_of_not_ge hnot
    obtain ⟨r, htr, hru, _hslope, hcross⟩ :=
      affine_crosses_left p q t u htu (hpmax q hq) hstrict
    have hrU : r ∈ U := Finset.mem_filter.mpr
      ⟨hcross ▸ affine_cross_mem_breakpoints lines p q hp hq, htr⟩
    have hurle : u ≤ r := by simpa using humin r hrU
    exact (not_le_of_gt hru) hurle
  obtain ⟨pl, hpl, hboundl⟩ := hbreak l hlC h0l (hlt.trans ht1)
  obtain ⟨pu, hpu, hboundu⟩ := hbreak u huC (ht0.trans htu) hu1
  have hleft : affineValue target l ≤ affineValue p l :=
    hboundl.trans (hlmax' pl hpl)
  have hright : affineValue target u ≤ affineValue p u :=
    hboundu.trans (humax' pu hpu)
  refine ⟨p, hp, ?_⟩
  by_cases hlu : l = u
  · have htl : t = l := by linarith
    simpa [htl] using hleft
  · exact affine_support_interpolate p target l t u hlt htu
      (lt_of_le_of_ne (hlt.trans htu) hlu) hleft hright

/-- A quadrant of the L1 unit circle, parametrized by one number. -/
def quadrantNormal (sx sy r : ℝ) : Point := (sx * r, sy * (1 - r))

/-- Projection of a point along a quadrant normal as an affine function. -/
def quadrantLine (sx sy : ℝ) (p : Point) : ℝ × ℝ :=
  (sx * p.1 - sy * p.2, sy * p.2)

theorem quadrant_line_value (sx sy r : ℝ) (p : Point) :
    affineValue (quadrantLine sx sy p) r = dot (quadrantNormal sx sy r) p := by
  dsimp [affineValue, quadrantLine, quadrantNormal, dot]
  ring

/-- The full support bound on a quadrant follows from checks at its finite
    site-pair breakpoints. -/
theorem finite_quadrant_support
    (sites : Finset Point) (hnonempty : sites.Nonempty)
    (center : Point) (h sx sy : ℝ)
    (hbreak : ∀ r ∈ affineBreakpoints (sites.image (quadrantLine sx sy)),
      0 ≤ r → r ≤ 1 →
      ∃ p ∈ sites,
        dot (quadrantNormal sx sy r) center ≤
          dot (quadrantNormal sx sy r) p + h)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ p ∈ sites,
      dot (quadrantNormal sx sy r) center ≤
        dot (quadrantNormal sx sy r) p + h := by
  classical
  let lines := sites.image (quadrantLine sx sy)
  let target : ℝ × ℝ :=
    (sx * center.1 - sy * center.2, sy * center.2 - h)
  have hlines : lines.Nonempty := hnonempty.image _
  have htarget (t : ℝ) :
      affineValue target t = dot (quadrantNormal sx sy t) center - h := by
    dsimp [target, affineValue, quadrantNormal, dot]
    ring
  have hbreak' : ∀ t ∈ affineBreakpoints lines, 0 ≤ t → t ≤ 1 →
      ∃ line ∈ lines, affineValue target t ≤ affineValue line t := by
    intro t ht ht0 ht1
    obtain ⟨p, hp, hbound⟩ := hbreak t ht ht0 ht1
    refine ⟨quadrantLine sx sy p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    rw [htarget, quadrant_line_value]
    linarith
  obtain ⟨line, hline, hbound⟩ :=
    finite_affine_envelope_of_breakpoints lines target hlines hbreak' r hr0 hr1
  obtain ⟨p, hp, hlineeq⟩ := Finset.mem_image.mp hline
  refine ⟨p, hp, ?_⟩
  rw [← hlineeq, htarget, quadrant_line_value] at hbound
  linarith

end
end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.affine_support_interpolate
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.affine_crosses_right
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.finite_affine_envelope_of_breakpoints
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.finite_quadrant_support
