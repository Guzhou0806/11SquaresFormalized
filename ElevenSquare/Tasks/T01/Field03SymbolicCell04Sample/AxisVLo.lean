import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.AxisULo

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
open ElevenSquare.Pending ElevenSquare.Tasks.T01 ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def polyVLo : Quartic := ⟨(172788692124586204836209472577/3820000000000000000000000000000), (345577383861464050670137527423/1910000000000000000000000000000), (-172788692124586204836209472577/3820000000000000000000000000000), 0, 0⟩

theorem polyVLo_check : polyVLo.BernsteinNonnegCheck (1/256) (1/128) := by
  norm_num [polyVLo, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem vlo_order (t : ℝ)
    (hlo : ((1/256 : ℚ) : ℝ) ≤ t) (hhi : t ≤ ((1/128 : ℚ) : ℝ)) :
    dot (chartNumeratorNormal t (0, 1)) (realPoint site1) ≤
      dot (chartNumeratorNormal t (0, 1)) (realPoint site0) := by
  have hp := quartic_bernstein_nonneg polyVLo (1/256) (1/128)
    polyVLo_check t hlo hhi
  have he : polyVLo.eval t =
      dot (chartNumeratorNormal t (0, 1)) (realPoint site0) -
        dot (chartNumeratorNormal t (0, 1)) (realPoint site1) := by
    dsimp [polyVLo, Quartic.eval, chartNumeratorNormal, realPoint, dot,
      site0, site1]
    push_cast
    ring
  rw [he] at hp
  exact sub_nonneg.mp hp

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
