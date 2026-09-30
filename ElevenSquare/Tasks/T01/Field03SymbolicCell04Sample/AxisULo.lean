import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MedianWorldBridge

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
open ElevenSquare.Pending ElevenSquare.Tasks.T01 ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def site0 : QPoint := ((3801351224026937993380638472577/3820000000000000000000000000000), (7429913755929289781925067472577/3820000000000000000000000000000))
def site1 : QPoint := ((2713958513015969924117/2500000000000000000000), (18997709591111789468819/10000000000000000000000))
def site2 : QPoint := ((1869077312324257697242572506767/1910000000000000000000000000000), (3817124574884991823543842826703/1910000000000000000000000000000))

def polyULo : Quartic := ⟨(63196599378422598895493459043/3820000000000000000000000000000), (-204335393840693865162618180829/1910000000000000000000000000000), (-63196599378422598895493459043/3820000000000000000000000000000), 0, 0⟩

theorem polyULo_check : polyULo.BernsteinNonnegCheck (1/256) (1/128) := by
  norm_num [polyULo, Quartic.BernsteinNonnegCheck,
    Quartic.bernsteinOn, Quartic.shift, Quartic.toBernstein]

theorem ulo_order (t : ℝ)
    (hlo : ((1/256 : ℚ) : ℝ) ≤ t) (hhi : t ≤ ((1/128 : ℚ) : ℝ)) :
    dot (chartNumeratorNormal t (1, 0)) (realPoint site2) ≤
      dot (chartNumeratorNormal t (1, 0)) (realPoint site0) := by
  have hp := quartic_bernstein_nonneg polyULo (1/256) (1/128)
    polyULo_check t hlo hhi
  have he : polyULo.eval t =
      dot (chartNumeratorNormal t (1, 0)) (realPoint site0) -
        dot (chartNumeratorNormal t (1, 0)) (realPoint site2) := by
    dsimp [polyULo, Quartic.eval, chartNumeratorNormal, realPoint, dot,
      site0, site2]
    push_cast
    ring
  rw [he] at hp
  exact sub_nonneg.mp hp

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Sample
