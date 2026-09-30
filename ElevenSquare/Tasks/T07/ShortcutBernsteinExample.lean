import ElevenSquare.Tasks.T07.ShortcutBernstein
import ElevenSquare.Tasks.T07.ShortcutCollisionChecker
import ElevenSquare.Tasks.T07.CaptureSeedGeometry
import Mathlib.Tactic.NormNum

/-! A representative endpoint-tight source collision inequality. At the
upper/right corner of the far15 row-family box, the strict margin is only
about 0.0066 in field units. The three rational Bernstein checks certify
the entire angular interval in one proof. -/
namespace ElevenSquare.Tasks.T07
noncomputable section

def far15ExampleDX : ℚ := 45936839/50000000-557/1000
def far15ExampleDY : ℚ := 103898071/50000000-2573/1000

theorem far15_example_interval (t : ℝ)
    (hlo : (233/256 : ℝ) ≤ t) (hhi : t ≤ 63/64) :
    0 < quadraticAt ((seedFieldScale/2-far15ExampleDX : ℚ) : ℝ)
      ((2*far15ExampleDY : ℚ) : ℝ)
      ((seedFieldScale/2+far15ExampleDX : ℚ) : ℝ) t := by
  apply quadratic_bernstein_pos_on _ _ _ (233/256 : ℝ) (63/64 : ℝ) t
    (by norm_num) hlo hhi
  · norm_num [quadraticAt, seedFieldScale, far15ExampleDX, far15ExampleDY]
  · norm_num [quadraticBernsteinMiddle, quadraticAt, seedFieldScale,
      far15ExampleDX, far15ExampleDY]
  · norm_num [quadraticAt, seedFieldScale, far15ExampleDX, far15ExampleDY]

/-- One complete four-sided field collision certificate for the worst
upper/right corner of the coarse far15 family box. -/
theorem far15_corner_certificate :
    FieldCollisionCert (seedFieldScale : ℝ)
      ((557/1000 : ℝ), (2573/1000 : ℝ))
      ((45936839/50000000 : ℝ), (103898071/50000000 : ℝ))
      (233/256 : ℝ) (63/64 : ℝ) := by
  norm_num [FieldCollisionCert, QuadraticIntervalCert, fieldDX, fieldDY,
    quadraticAt, quadraticBernsteinMiddle, seedFieldScale]

end
end ElevenSquare.Tasks.T07
