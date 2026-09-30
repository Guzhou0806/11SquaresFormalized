import ElevenSquare.Tasks.T01.Root
import ElevenSquare.Pending.S06_BaselinePolyhedral

namespace ElevenSquare.Tasks.T01
open ElevenSquare.Pending
noncomputable section

def baselineCos (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
def baselineSin (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)
def baselineTrig (t : ℚ) : QPoint :=
  ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))

theorem baseline_trig_cast (t : ℚ) : realPoint (baselineTrig t) = chartAxis (t : ℝ) := by
  ext <;> simp [realPoint, baselineTrig, chartAxis]

theorem baseline_cos_antitone (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    baselineCos b ≤ baselineCos a := by
  have hda : 0 < 1 + a ^ 2 := by positivity
  have hdb : 0 < 1 + b ^ 2 := by positivity
  unfold baselineCos
  apply (div_le_div_iff₀ hdb hda).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ b + a by linarith)]

theorem baseline_sin_monotone (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    baselineSin a ≤ baselineSin b := by
  have hda : 0 < 1 + a ^ 2 := by positivity
  have hdb : 0 < 1 + b ^ 2 := by positivity
  have hab1 : a * b ≤ 1 :=
    (mul_le_mul_of_nonneg_right (hab.trans hb) (ha.trans hab)).trans (by simpa using hb)
  have hprod := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hab1)
  unfold baselineSin
  apply (div_le_div_iff₀ hda hdb).mpr
  nlinarith

theorem baseline_concave_quadratic_nonneg (a b c l u t : ℝ)
    (ha : a ≤ 0) (hlt : l ≤ t) (htu : t ≤ u)
    (hl : 0 ≤ a * l ^ 2 + b * l + c)
    (hu : 0 ≤ a * u ^ 2 + b * u + c) :
    0 ≤ a * t ^ 2 + b * t + c := by
  by_cases he : l = u
  · have ht : t = l := by linarith
    simpa [ht] using hl
  · have hgap : 0 < u - l := by
      apply lt_of_not_ge
      intro hn
      apply he
      linarith
    have h1 := mul_nonneg (sub_nonneg.mpr htu) hl
    have h2 := mul_nonneg (sub_nonneg.mpr hlt) hu
    have h3 : 0 ≤ (u - l) * (-a) * (t - l) * (u - t) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg hgap.le (neg_nonneg.mpr ha))
        (sub_nonneg.mpr hlt)) (sub_nonneg.mpr htu)
    have hid : (u - l) * (a * t ^ 2 + b * t + c) =
        (u - t) * (a * l ^ 2 + b * l + c) +
        (t - l) * (a * u ^ 2 + b * u + c) +
        (u - l) * (-a) * (t - l) * (u - t) := by ring
    have hnon : 0 ≤ (u - l) * (a * t ^ 2 + b * t + c) := by rw [hid]; linarith
    by_contra hh
    have hneg := mul_neg_of_pos_of_neg hgap (lt_of_not_ge hh)
    exact (not_lt_of_ge hnon) hneg

def BaselineWallCheck (lo hi h : ℚ) : Prop :=
  0 ≤ h ∧
  0 ≤ 1 - 2 * h + 2 * lo - (1 + 2 * h) * lo ^ 2 ∧
  0 ≤ 1 - 2 * h + 2 * hi - (1 + 2 * h) * hi ^ 2

instance (lo hi h : ℚ) : Decidable (BaselineWallCheck lo hi h) := by
  unfold BaselineWallCheck
  infer_instance

theorem baseline_wall_check_sound (lo hi h : ℚ) (hc : BaselineWallCheck lo hi h)
    (t : ℝ) (hlo : (lo : ℝ) ≤ t) (hhi : t ≤ (hi : ℝ)) :
    (h : ℝ) ≤ (baselineCos t + baselineSin t) / 2 := by
  have hn : (0 : ℝ) ≤ h := by exact_mod_cast hc.1
  have hl : (0 : ℝ) ≤ 1 - 2 * (h : ℝ) + 2 * (lo : ℝ) -
      (1 + 2 * (h : ℝ)) * (lo : ℝ) ^ 2 := by exact_mod_cast hc.2.1
  have hu : (0 : ℝ) ≤ 1 - 2 * (h : ℝ) + 2 * (hi : ℝ) -
      (1 + 2 * (h : ℝ)) * (hi : ℝ) ^ 2 := by exact_mod_cast hc.2.2
  have ht := baseline_concave_quadratic_nonneg (-(1 + 2 * (h : ℝ))) 2
    (1 - 2 * (h : ℝ)) (lo : ℝ) (hi : ℝ) t (by linarith) hlo hhi
    (by nlinarith [hl]) (by nlinarith [hu])
  have hd : (0 : ℝ) < 1 + t ^ 2 := by positivity
  unfold baselineCos baselineSin
  rw [← add_div]
  apply (le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)).mpr
  apply (le_div_iff₀ hd).mpr
  nlinarith

def baselineCorner (q : UnitSquare) (a b : ℝ) : Point :=
  q.center + a • q.axis + b • perp q.axis

theorem baseline_corner_local (q : UnitSquare) (a b : ℝ) :
    localX q (baselineCorner q a b) = a ∧ localY q (baselineCorner q a b) = b := by
  have hunit := q.axis_unit
  dsimp [normSq, dot] at hunit
  dsimp [localX, localY, baselineCorner, dot, perp]
  constructor
  · linear_combination a * hunit
  · linear_combination b * hunit

theorem baseline_corner_closed (q : UnitSquare) (a b : ℝ)
    (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) :
    ClosedSquare q (baselineCorner q a b) := by
  have h := baseline_corner_local q a b
  simpa [ClosedSquare, h.1, h.2] using And.intro ha hb

theorem baseline_contained_axis_bounds (q : UnitSquare) (S : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer S p) :
    (q.axis.1 + q.axis.2) / 2 ≤ q.center.1 ∧
    q.center.1 ≤ S - (q.axis.1 + q.axis.2) / 2 ∧
    (q.axis.1 + q.axis.2) / 2 ≤ q.center.2 ∧
    q.center.2 ≤ S - (q.axis.1 + q.axis.2) / 2 := by
  have hpp := hc _ (baseline_corner_closed q (1 / 2) (1 / 2)
    (by norm_num [abs_le]) (by norm_num [abs_le]))
  have hpm := hc _ (baseline_corner_closed q (1 / 2) (-1 / 2)
    (by norm_num [abs_le]) (by norm_num [abs_le]))
  have hmp := hc _ (baseline_corner_closed q (-1 / 2) (1 / 2)
    (by norm_num [abs_le]) (by norm_num [abs_le]))
  have hmm := hc _ (baseline_corner_closed q (-1 / 2) (-1 / 2)
    (by norm_num [abs_le]) (by norm_num [abs_le]))
  dsimp [InContainer, baselineCorner, perp] at hpp hpm hmp hmm
  rcases hpp with ⟨hpp1, hpp2, hpp3, hpp4⟩
  rcases hpm with ⟨hpm1, hpm2, hpm3, hpm4⟩
  rcases hmp with ⟨hmp1, hmp2, hmp3, hmp4⟩
  rcases hmm with ⟨hmm1, hmm2, hmm3, hmm4⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

def baselineSlab (cell : Fin 16) (h : ℚ) : Polygon :=
  [⟨-1, 0, -h⟩, ⟨1, 0, baselineRationalCap - h⟩,
   ⟨0, -1, -h⟩, ⟨0, 1, baselineRationalCap - h⟩] ++ baselineCellPolygon cell

theorem baseline_slab_contains (q : UnitSquare) (cell : Fin 16) (lo hi h : ℚ)
    (t : ℝ) (hc : BaselineWallCheck lo hi h)
    (hlo : (lo : ℝ) ≤ t) (hhi : t ≤ (hi : ℝ)) (ha : q.axis = chartAxis t)
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : q.center ∈ (baselineCellPolygon cell).carrier) :
    q.center ∈ (baselineSlab cell h).carrier := by
  have hh := baseline_wall_check_sound lo hi h hc t hlo hhi
  have hb := baseline_contained_axis_bounds q coverCap hcont
  rw [ha] at hb
  change (baselineCos t + baselineSin t) / 2 ≤ q.center.1 ∧
    q.center.1 ≤ coverCap - (baselineCos t + baselineSin t) / 2 ∧
    (baselineCos t + baselineSin t) / 2 ≤ q.center.2 ∧
    q.center.2 ≤ coverCap - (baselineCos t + baselineSin t) / 2 at hb
  rcases hb with ⟨hxlo, hxhi, hylo, hyhi⟩
  intro e he
  rcases List.mem_append.mp he with he | he
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    all_goals
      dsimp [Halfplane.contains]
      push_cast
      try rw [baselineRationalCap_cast]
      linarith
  · exact hcell e he

end
end ElevenSquare.Tasks.T01
