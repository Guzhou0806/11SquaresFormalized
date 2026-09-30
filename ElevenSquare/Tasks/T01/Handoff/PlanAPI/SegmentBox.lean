import ElevenSquare.Pending.S06_BaselinePolyhedral

namespace ElevenSquare.Tasks.T01.Handoff.PlanAPI

/-- A segment with both coordinates nondecreasing meets a centered closed
    square if the four axial support bounds and two perpendicular support
    bounds hold. The parameter is chosen as the larger lower-coordinate
    crossing time. -/
theorem increasing_segment_hits_closed_square
    (a b dx dy h : ℝ) (hh : 0 ≤ h) (hdx : 0 < dx) (hdy : 0 < dy)
    (hx0 : a ≤ h) (hx1 : -h ≤ a + dx)
    (hy0 : b ≤ h) (hy1 : -h ≤ b + dy)
    (hc1 : a * dy - b * dx ≤ h * (dx + dy))
    (hc2 : b * dx - a * dy ≤ h * (dx + dy)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      -h ≤ a + t * dx ∧ a + t * dx ≤ h ∧
      -h ≤ b + t * dy ∧ b + t * dy ≤ h := by
  let lx := (-h - a) / dx
  let ly := (-h - b) / dy
  let ux := (h - a) / dx
  let uy := (h - b) / dy
  let t := max 0 (max lx ly)
  have hlx : lx ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
  have hly : ly ≤ t := le_trans (le_max_right _ _) (le_max_right _ _)
  have ht0 : 0 ≤ t := le_max_left _ _
  have hlx1 : lx ≤ 1 := by
    apply (div_le_iff₀ hdx).mpr
    dsimp [lx]
    linarith
  have hly1 : ly ≤ 1 := by
    apply (div_le_iff₀ hdy).mpr
    dsimp [ly]
    linarith
  have ht1 : t ≤ 1 := max_le (by norm_num) (max_le hlx1 hly1)
  have h0ux : 0 ≤ ux := div_nonneg (sub_nonneg.mpr hx0) hdx.le
  have h0uy : 0 ≤ uy := div_nonneg (sub_nonneg.mpr hy0) hdy.le
  have hlxux : lx ≤ ux := by
    dsimp [lx, ux]
    exact (div_le_div_iff₀ hdx hdx).mpr (by nlinarith)
  have hlyuy : ly ≤ uy := by
    dsimp [ly, uy]
    exact (div_le_div_iff₀ hdy hdy).mpr (by nlinarith)
  have hlyux : ly ≤ ux := by
    dsimp [ly, ux]
    exact (div_le_div_iff₀ hdy hdx).mpr (by nlinarith [hc1])
  have hlxuy : lx ≤ uy := by
    dsimp [lx, uy]
    exact (div_le_div_iff₀ hdx hdy).mpr (by nlinarith [hc2])
  have htux : t ≤ ux := max_le h0ux (max_le hlxux hlyux)
  have htuy : t ≤ uy := max_le h0uy (max_le hlxuy hlyuy)
  refine ⟨t, ht0, ht1, ?_, ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_right hlx hdx.le
    dsimp [lx] at hh
    field_simp at hh
    linarith
  · have hh := mul_le_mul_of_nonneg_right htux hdx.le
    dsimp [ux] at hh
    field_simp at hh
    linarith
  · have hh := mul_le_mul_of_nonneg_right hly hdy.le
    dsimp [ly] at hh
    field_simp at hh
    linarith
  · have hh := mul_le_mul_of_nonneg_right htuy hdy.le
    dsimp [uy] at hh
    field_simp at hh
    linarith

/-- The one-coordinate version also handles a stationary coordinate. -/
theorem increasing_segment_hits_closed_interval
    (a d h : ℝ) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (ha0 : a ≤ h) (ha1 : -h ≤ a + d) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ -h ≤ a + t * d ∧ a + t * d ≤ h := by
  by_cases hdp : 0 < d
  · let lo := (-h - a) / d
    let hi := (h - a) / d
    let t := max 0 lo
    have hlo : lo ≤ t := le_max_right _ _
    have ht0 : 0 ≤ t := le_max_left _ _
    have hlo1 : lo ≤ 1 := by
      dsimp [lo]
      exact (div_le_iff₀ hdp).mpr (by linarith)
    have ht1 : t ≤ 1 := max_le (by norm_num) hlo1
    have h0hi : 0 ≤ hi := div_nonneg (sub_nonneg.mpr ha0) hdp.le
    have hlohi : lo ≤ hi := by
      dsimp [lo, hi]
      exact (div_le_div_iff₀ hdp hdp).mpr (by nlinarith)
    have hthi : t ≤ hi := max_le h0hi hlohi
    refine ⟨t, ht0, ht1, ?_, ?_⟩
    · have hm := mul_le_mul_of_nonneg_right hlo hdp.le
      dsimp [lo] at hm
      field_simp at hm
      linarith
    · have hm := mul_le_mul_of_nonneg_right hthi hdp.le
      dsimp [hi] at hm
      field_simp at hm
      linarith
  · have hd0 : d = 0 := le_antisymm (le_of_not_gt hdp) hd
    refine ⟨0, by norm_num, by norm_num, ?_, ?_⟩
    · simpa [hd0] using ha1
    · simpa [hd0] using ha0

/-- The six support inequalities also handle horizontal and vertical
    segments; no nondegeneracy condition is needed. -/
theorem nondecreasing_segment_hits_closed_square
    (a b dx dy h : ℝ) (hh : 0 ≤ h) (hdx : 0 ≤ dx) (hdy : 0 ≤ dy)
    (hx0 : a ≤ h) (hx1 : -h ≤ a + dx)
    (hy0 : b ≤ h) (hy1 : -h ≤ b + dy)
    (hc1 : a * dy - b * dx ≤ h * (dx + dy))
    (hc2 : b * dx - a * dy ≤ h * (dx + dy)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      -h ≤ a + t * dx ∧ a + t * dx ≤ h ∧
      -h ≤ b + t * dy ∧ b + t * dy ≤ h := by
  by_cases hdxp : 0 < dx
  · by_cases hdyp : 0 < dy
    · exact increasing_segment_hits_closed_square a b dx dy h hh hdxp hdyp
        hx0 hx1 hy0 hy1 hc1 hc2
    · have hdy0 : dy = 0 := le_antisymm (le_of_not_gt hdyp) hdy
      obtain ⟨t, ht0, ht1, hxl, hxu⟩ :=
        increasing_segment_hits_closed_interval a dx h hh hdx hx0 hx1
      refine ⟨t, ht0, ht1, hxl, hxu, ?_, ?_⟩
      · simpa [hdy0] using hy1
      · simpa [hdy0] using hy0
  · have hdx0 : dx = 0 := le_antisymm (le_of_not_gt hdxp) hdx
    obtain ⟨t, ht0, ht1, hyl, hyu⟩ :=
      increasing_segment_hits_closed_interval b dy h hh hdy hy0 hy1
    refine ⟨t, ht0, ht1, ?_, ?_, hyl, hyu⟩
    · simpa [hdx0] using hx1
    · simpa [hdx0] using hx0

private theorem axis_support_cases (a d h : ℝ)
    (hmin : min a (a + d) ≤ h)
    (hmax : -h ≤ max a (a + d)) :
    (0 ≤ d → a ≤ h ∧ -h ≤ a + d) ∧
    (d ≤ 0 → -h ≤ a ∧ a + d ≤ h) := by
  constructor
  · intro hd
    have ha : a ≤ a + d := by linarith
    constructor
    · simpa [min_eq_left ha] using hmin
    · simpa [max_eq_right ha] using hmax
  · intro hd
    have ha : a + d ≤ a := by linarith
    constructor
    · simpa [max_eq_left ha] using hmax
    · simpa [min_eq_right ha] using hmin

/-- A support criterion for an arbitrarily directed planar segment to meet
    the centered closed square. The axial tests say each coordinate interval
    overlaps the square; the two perpendicular tests prevent the intervals
    from being reached at disjoint segment parameters. -/
theorem segment_hits_closed_square
    (a b dx dy h : ℝ) (hh : 0 ≤ h)
    (hxmin : min a (a + dx) ≤ h)
    (hxmax : -h ≤ max a (a + dx))
    (hymin : min b (b + dy) ≤ h)
    (hymax : -h ≤ max b (b + dy))
    (hcross : |a * dy - b * dx| ≤ h * (|dx| + |dy|)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      -h ≤ a + t * dx ∧ a + t * dx ≤ h ∧
      -h ≤ b + t * dy ∧ b + t * dy ≤ h := by
  obtain ⟨hxp, hxm⟩ := axis_support_cases a dx h hxmin hxmax
  obtain ⟨hyp, hym⟩ := axis_support_cases b dy h hymin hymax
  have hcLo := (abs_le.mp hcross).1
  have hcHi := (abs_le.mp hcross).2
  rcases le_total 0 dx with hdxp | hdxm
  · rcases le_total 0 dy with hdyp | hdym
    · rw [abs_of_nonneg hdxp, abs_of_nonneg hdyp] at hcLo hcHi
      exact nondecreasing_segment_hits_closed_square a b dx dy h hh hdxp hdyp
        (hxp hdxp).1 (hxp hdxp).2 (hyp hdyp).1 (hyp hdyp).2
        hcHi (by linarith)
    · rw [abs_of_nonneg hdxp, abs_of_nonpos hdym] at hcLo hcHi
      obtain ⟨t, ht0, ht1, hxl, hxu, hyl, hyu⟩ :=
        nondecreasing_segment_hits_closed_square a (-b) dx (-dy) h hh
          hdxp (by linarith) (hxp hdxp).1 (by linarith [(hxp hdxp).2])
          (by linarith [(hym hdym).1]) (by linarith [(hym hdym).2])
          (by nlinarith [hcLo]) (by nlinarith [hcHi])
      exact ⟨t, ht0, ht1, hxl, hxu, by linarith, by linarith⟩
  · rcases le_total 0 dy with hdyp | hdym
    · rw [abs_of_nonpos hdxm, abs_of_nonneg hdyp] at hcLo hcHi
      obtain ⟨t, ht0, ht1, hxl, hxu, hyl, hyu⟩ :=
        nondecreasing_segment_hits_closed_square (-a) b (-dx) dy h hh
          (by linarith) hdyp (by linarith [(hxm hdxm).1])
          (by linarith [(hxm hdxm).2]) (hyp hdyp).1 (hyp hdyp).2
          (by nlinarith [hcLo]) (by nlinarith [hcHi])
      exact ⟨t, ht0, ht1, by linarith, by linarith, hyl, hyu⟩
    · rw [abs_of_nonpos hdxm, abs_of_nonpos hdym] at hcLo hcHi
      obtain ⟨t, ht0, ht1, hxl, hxu, hyl, hyu⟩ :=
        nondecreasing_segment_hits_closed_square (-a) (-b) (-dx) (-dy) h hh
          (by linarith) (by linarith) (by linarith [(hxm hdxm).1])
          (by linarith [(hxm hdxm).2]) (by linarith [(hym hdym).1])
          (by linarith [(hym hdym).2]) (by nlinarith [hcHi])
          (by nlinarith [hcLo])
      exact ⟨t, ht0, ht1, by linarith, by linarith, by linarith, by linarith⟩

/-- Strict support bounds give a point of the segment in the open square.
    The proof first reduces the half-width by a small positive amount, then
    applies the closed theorem. Distinct endpoints ensure a nonzero direction. -/
theorem segment_hits_open_square
    (a b dx dy h : ℝ) (hh : 0 < h)
    (hs : 0 < |dx| + |dy|)
    (hxmin : min a (a + dx) < h)
    (hxmax : -h < max a (a + dx))
    (hymin : min b (b + dy) < h)
    (hymax : -h < max b (b + dy))
    (hcross : |a * dy - b * dx| < h * (|dx| + |dy|)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      -h < a + t * dx ∧ a + t * dx < h ∧
      -h < b + t * dy ∧ b + t * dy < h := by
  let radius := max 0 (max (min a (a + dx))
    (max (-max a (a + dx))
    (max (min b (b + dy))
    (max (-max b (b + dy))
      (|a * dy - b * dx| / (|dx| + |dy|))))))
  have hcross' : |a * dy - b * dx| / (|dx| + |dy|) < h :=
    (div_lt_iff₀ hs).mpr hcross
  have hradius : radius < h := by
    dsimp [radius]
    apply max_lt hh
    apply max_lt hxmin
    apply max_lt (by linarith [hxmax])
    apply max_lt hymin
    apply max_lt (by linarith [hymax])
    exact hcross'
  have hzero : 0 ≤ radius := by dsimp [radius]; exact le_max_left _ _
  let inner := (radius + h) / 2
  have hinner0 : 0 ≤ inner := by dsimp [inner]; linarith
  have hrinner : radius < inner := by dsimp [inner]; linarith
  have hinnerh : inner < h := by dsimp [inner]; linarith
  have hxmin' : min a (a + dx) ≤ inner := by
    have hr : min a (a + dx) ≤ radius := by simp [radius]
    linarith
  have hxmax' : -inner ≤ max a (a + dx) := by
    have hr : -max a (a + dx) ≤ radius := by simp [radius]
    linarith
  have hymin' : min b (b + dy) ≤ inner := by
    have hr : min b (b + dy) ≤ radius := by simp [radius]
    linarith
  have hymax' : -inner ≤ max b (b + dy) := by
    have hr : -max b (b + dy) ≤ radius := by simp [radius]
    linarith
  have hcrossinner : |a * dy - b * dx| ≤ inner * (|dx| + |dy|) := by
    have hr : |a * dy - b * dx| / (|dx| + |dy|) ≤ radius := by
      simp [radius]
    have hm := mul_le_mul_of_nonneg_right (hr.trans hrinner.le) hs.le
    have he : (|a * dy - b * dx| / (|dx| + |dy|)) *
        (|dx| + |dy|) = |a * dy - b * dx| := by
      field_simp [ne_of_gt hs]
    rw [he] at hm
    exact hm
  obtain ⟨t, ht0, ht1, hxl, hxu, hyl, hyu⟩ :=
    segment_hits_closed_square a b dx dy inner hinner0
      hxmin' hxmax' hymin' hymax' hcrossinner
  exact ⟨t, ht0, ht1, by linarith, by linarith, by linarith, by linarith⟩

end ElevenSquare.Tasks.T01.Handoff.PlanAPI

#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.increasing_segment_hits_closed_square
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.nondecreasing_segment_hits_closed_square
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.segment_hits_closed_square
#print axioms ElevenSquare.Tasks.T01.Handoff.PlanAPI.segment_hits_open_square
