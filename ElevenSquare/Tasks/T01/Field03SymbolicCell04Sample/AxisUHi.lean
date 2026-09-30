import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.AxisULo

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
open ElevenSquare.Pending ElevenSquare.Tasks.T01 ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def polyUHi : Quartic := ⟨(345577383861464050670137527423/3820000000000000000000000000000), (-172788692124586204836209472577/1910000000000000000000000000000), (-345577383861464050670137527423/3820000000000000000000000000000), 0, 0⟩

theorem polyUHi_check : polyUHi.BernsteinNonnegCheck (1/256) (1/128) := by
  norm_num [polyUHi, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem uhi_order (t : ℝ)
    (hlo : ((1/256 : ℚ) : ℝ) ≤ t) (hhi : t ≤ ((1/128 : ℚ) : ℝ)) :
    dot (chartNumeratorNormal t (1, 0)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (1, 0)) (realPoint site1) := by
  have hp := quartic_bernstein_nonneg polyUHi (1/256) (1/128)
    polyUHi_check t hlo hhi
  have he : polyUHi.eval t =
      dot (chartNumeratorNormal t (1, 0)) (realPoint site1) -
        dot (chartNumeratorNormal t (1, 0)) (realPoint site0) := by
    dsimp [polyUHi, Quartic.eval, chartNumeratorNormal, realPoint, dot,
      site1, site0]
    push_cast
    ring
  rw [he] at hp
  exact sub_nonneg.mp hp

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
