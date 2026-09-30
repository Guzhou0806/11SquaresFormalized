import ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample.AxisULo

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
open ElevenSquare.Pending ElevenSquare.Tasks.T01 ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def polyVHi : Quartic := ⟨(204335393840693865162618180829/3820000000000000000000000000000), (63196599378422598895493459043/1910000000000000000000000000000), (-204335393840693865162618180829/3820000000000000000000000000000), 0, 0⟩

theorem polyVHi_check : polyVHi.BernsteinNonnegCheck (1/256) (1/128) := by
  norm_num [polyVHi, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem vhi_order (t : ℝ)
    (hlo : ((1/256 : ℚ) : ℝ) ≤ t) (hhi : t ≤ ((1/128 : ℚ) : ℝ)) :
    dot (chartNumeratorNormal t (0, 1)) (realPoint site0) ≤
      dot (chartNumeratorNormal t (0, 1)) (realPoint site2) := by
  have hp := quartic_bernstein_nonneg polyVHi (1/256) (1/128)
    polyVHi_check t hlo hhi
  have he : polyVHi.eval t =
      dot (chartNumeratorNormal t (0, 1)) (realPoint site2) -
        dot (chartNumeratorNormal t (0, 1)) (realPoint site0) := by
    dsimp [polyVHi, Quartic.eval, chartNumeratorNormal, realPoint, dot,
      site2, site0]
    push_cast
    ring
  rw [he] at hp
  exact sub_nonneg.mp hp

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
