import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.AxisULo

namespace ElevenSquare.Tasks.T01.Field03SymbolicMedianRep002
open ElevenSquare.Pending ElevenSquare.Tasks.T01 ElevenSquare.Tasks.T01.Handoff.PlanAPI
open ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample (site0 site1 site2)
noncomputable section

def polyULo : Quartic := ⟨(-63196599378422598895493459043/3820000000000000000000000000000), (204335393840693865162618180829/1910000000000000000000000000000), (63196599378422598895493459043/3820000000000000000000000000000), 0, 0⟩

theorem polyULo_check : polyULo.BernsteinNonnegCheck (619/4096) (897/2048) := by
  norm_num [polyULo, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem ULo_order (t : ℝ)
    (hlo : (((619/4096) : ℚ) : ℝ) ≤ t)
    (hhi : t ≤ (((897/2048) : ℚ) : ℝ)) :
    dot (chartNumeratorNormal t (1, 0)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (1, 0)) (realPoint site2) := by
  have hp := quartic_bernstein_nonneg polyULo (619/4096) (897/2048)
    polyULo_check t hlo hhi
  have he : polyULo.eval t =
      dot (chartNumeratorNormal t (1, 0)) (realPoint site2) -
        dot (chartNumeratorNormal t (1, 0)) (realPoint site0) := by
    dsimp [polyULo, Quartic.eval, chartNumeratorNormal, realPoint, dot,
      site0, site2]
    push_cast
    ring
  rw [he] at hp
  exact sub_nonneg.mp hp

def polyUHi : Quartic := ⟨(204386991619943324782815493233/1910000000000000000000000000000), (-188562042982640034999413826703/955000000000000000000000000000), (-204386991619943324782815493233/1910000000000000000000000000000), 0, 0⟩

theorem polyUHi_check : polyUHi.BernsteinNonnegCheck (619/4096) (897/2048) := by
  norm_num [polyUHi, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem UHi_order (t : ℝ)
    (hlo : (((619/4096) : ℚ) : ℝ) ≤ t)
    (hhi : t ≤ (((897/2048) : ℚ) : ℝ)) :
    dot (chartNumeratorNormal t (1, 0)) (realPoint site2) ≤
      dot (chartNumeratorNormal t (1, 0)) (realPoint site1) := by
  have hp := quartic_bernstein_nonneg polyUHi (619/4096) (897/2048)
    polyUHi_check t hlo hhi
  have he : polyUHi.eval t =
      dot (chartNumeratorNormal t (1, 0)) (realPoint site1) -
        dot (chartNumeratorNormal t (1, 0)) (realPoint site2) := by
    dsimp [polyUHi, Quartic.eval, chartNumeratorNormal, realPoint, dot,
      site2, site1]
    push_cast
    ring
  rw [he] at hp
  exact sub_nonneg.mp hp

def polyVLo : Quartic := ⟨(172788692124586204836209472577/3820000000000000000000000000000), (345577383861464050670137527423/1910000000000000000000000000000), (-172788692124586204836209472577/3820000000000000000000000000000), 0, 0⟩

theorem polyVLo_check : polyVLo.BernsteinNonnegCheck (619/4096) (897/2048) := by
  norm_num [polyVLo, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem VLo_order (t : ℝ)
    (hlo : (((619/4096) : ℚ) : ℝ) ≤ t)
    (hhi : t ≤ (((897/2048) : ℚ) : ℝ)) :
    dot (chartNumeratorNormal t (0, 1)) (realPoint site1) ≤
      dot (chartNumeratorNormal t (0, 1)) (realPoint site0) := by
  have hp := quartic_bernstein_nonneg polyVLo (619/4096) (897/2048)
    polyVLo_check t hlo hhi
  have he : polyVLo.eval t =
      dot (chartNumeratorNormal t (0, 1)) (realPoint site0) -
        dot (chartNumeratorNormal t (0, 1)) (realPoint site1) := by
    dsimp [polyVLo, Quartic.eval, chartNumeratorNormal, realPoint, dot,
      site1, site0]
    push_cast
    ring
  rw [he] at hp
  exact sub_nonneg.mp hp

def polyVHi : Quartic := ⟨(204335393840693865162618180829/3820000000000000000000000000000), (63196599378422598895493459043/1910000000000000000000000000000), (-204335393840693865162618180829/3820000000000000000000000000000), 0, 0⟩

theorem polyVHi_check : polyVHi.BernsteinNonnegCheck (619/4096) (897/2048) := by
  norm_num [polyVHi, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem VHi_order (t : ℝ)
    (hlo : (((619/4096) : ℚ) : ℝ) ≤ t)
    (hhi : t ≤ (((897/2048) : ℚ) : ℝ)) :
    dot (chartNumeratorNormal t (0, 1)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (0, 1)) (realPoint site2) := by
  have hp := quartic_bernstein_nonneg polyVHi (619/4096) (897/2048)
    polyVHi_check t hlo hhi
  have he : polyVHi.eval t =
      dot (chartNumeratorNormal t (0, 1)) (realPoint site2) -
        dot (chartNumeratorNormal t (0, 1)) (realPoint site0) := by
    dsimp [polyVHi, Quartic.eval, chartNumeratorNormal, realPoint, dot,
      site0, site2]
    push_cast
    ring
  rw [he] at hp
  exact sub_nonneg.mp hp

end
end ElevenSquare.Tasks.T01.Field03SymbolicMedianRep002
