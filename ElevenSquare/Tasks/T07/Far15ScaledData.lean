import ElevenSquare.Tasks.T07.Far15Scaled

/-! Nineteen complete source rows certified in the correct physical scale. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def far15Rows220to238 : List Far15ArchivedRow :=
  far15Rows220to239.take 19

def far15ScaledRatBox (v : QPoint) : Prop :=
  (1/2 : ℚ) ≤ v.1 ∧ v.1 ≤ 557/1000 ∧
  (2466/1000 : ℚ) ≤ v.2 ∧ v.2 ≤ 2573/1000

theorem far15_scaled_data_valid :
    ∀ r ∈ far15Rows220to238,
      (233/256 : ℚ) ≤ r.lo ∧ r.hi ≤ 63/64 ∧
      (∀ v ∈ r.vertices, far15ScaledRatBox v) := by
  intro r hr
  simp only [far15Rows220to238, far15Rows220to239,
    List.take, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [far15ScaledRatBox, Rat.divInt]

private theorem far15_scaled_hull_box (r : Far15ArchivedRow)
    (hv : ∀ v ∈ r.vertices, far15ScaledRatBox v)
    {p : Point} (hp : p ∈ rationalHull r.vertices) :
    (1/2 : ℝ) ≤ p.1 ∧ p.1 ≤ 557/1000 ∧
      (2466/1000 : ℝ) ≤ p.2 ∧ p.2 ≤ 2573/1000 := by
  let box : Set Point := {p |
    (1/2 : ℝ) ≤ p.1 ∧ p.1 ≤ 557/1000 ∧
    (2466/1000 : ℝ) ≤ p.2 ∧ p.2 ≤ 2573/1000}
  have hconv : Convex ℝ box := by
    have hs : box = (Set.Icc (1/2 : ℝ) (557/1000) ×ˢ
        Set.Icc (2466/1000 : ℝ) (2573/1000)) := by
      ext p
      simp only [box, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc]
      tauto
    rw [hs]
    exact (convex_Icc _ _).prod (convex_Icc _ _)
  have hbase : {p : Point | ∃ v ∈ r.vertices, p = realPoint v} ⊆ box := by
    rintro p ⟨v, hmem, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hv v hmem
    have h1' : (((1/2 : ℚ) : ℝ)) ≤ (v.1 : ℝ) := by exact_mod_cast h1
    have h2' : (v.1 : ℝ) ≤ (((557/1000 : ℚ) : ℝ)) := by exact_mod_cast h2
    have h3' : (((2466/1000 : ℚ) : ℝ)) ≤ (v.2 : ℝ) := by exact_mod_cast h3
    have h4' : (v.2 : ℝ) ≤ (((2573/1000 : ℚ) : ℝ)) := by exact_mod_cast h4
    change (1/2 : ℝ) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) ≤ 557/1000 ∧
      (2466/1000 : ℝ) ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) ≤ 2573/1000
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
      (show (((1/2 : ℚ) : ℝ)) ≤ (v.1 : ℝ) ∧
        (v.1 : ℝ) ≤ (((557/1000 : ℚ) : ℝ)) ∧
        (((2466/1000 : ℚ) : ℝ)) ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) ≤ (((2573/1000 : ℚ) : ℝ)) from
        ⟨h1', h2', h3', h4'⟩)
  exact convexHull_min hbase hconv hp

/-- Exact, scaled, whole-domain strict collision for every archived row
220–238. The coordinate equation is explicit and scales only the *certificate
coordinates*, never the physical square. -/
theorem far15_scaled_family_collision (r : Far15ArchivedRow)
    (hr : r ∈ far15Rows220to238) (q : UnitSquare)
    (pField : Point) (hc : pField ∈ rationalHull r.vertices)
    (hcenter : q.center =
      (pField.1/fieldScale,pField.2/fieldScale))
    (ha : ∃ t : ℝ, (r.lo : ℝ) ≤ t ∧ t ≤ (r.hi : ℝ) ∧
      q.axis = chartAxis t) :
    OpenSquare q far15PhysicalWitness := by
  obtain ⟨hlo, hhi, hv⟩ := far15_scaled_data_valid r hr
  obtain ⟨t, htlo, hthi, haxis⟩ := ha
  have hlo' : (((233/256 : ℚ) : ℝ)) ≤ (r.lo : ℝ) := by
    exact_mod_cast hlo
  have hhi' : (r.hi : ℝ) ≤ (((63/64 : ℚ) : ℝ)) := by
    exact_mod_cast hhi
  apply far15_scaled_box_collision q pField hcenter
    (far15_scaled_hull_box r hv hc)
  refine ⟨t, ?_, ?_, haxis⟩
  · have h := le_trans hlo' htlo
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  · have h := le_trans hthi hhi'
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h

theorem far15_scaled_family_excluded {S : ℝ} (P : Packing 11 S)
    (st : PoseState) (hstate : StateHolds P st)
    (howned : far15PhysicalWitness ∈
      rationalHull (st.owned ⟨6, by decide⟩))
    (r : Far15ArchivedRow) (hr : r ∈ far15Rows220to238)
    (pField : Point) (hc : pField ∈ rationalHull r.vertices)
    (hcenter : (P.squares ⟨5, by decide⟩).center =
      (pField.1/fieldScale,pField.2/fieldScale))
    (ha : ∃ t : ℝ, (r.lo : ℝ) ≤ t ∧ t ≤ (r.hi : ℝ) ∧
      (P.squares ⟨5, by decide⟩).axis = chartAxis t) : False := by
  have hother := hstate.2 ⟨6, by decide⟩ howned
  have htarget := far15_scaled_family_collision r hr
    (P.squares ⟨5, by decide⟩) pField hc hcenter ha
  exact P.interior_disjoint ⟨5, by decide⟩ ⟨6, by decide⟩
    (by decide) far15PhysicalWitness ⟨htarget, hother⟩

end
end ElevenSquare.Tasks.T07
