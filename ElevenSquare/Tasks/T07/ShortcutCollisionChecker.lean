import ElevenSquare.Tasks.T07.ShortcutBernstein
import ElevenSquare.Pending.Types
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! A single geometric bridge for rational angle-interval collision checks.
The four premise quadratics have rational coefficients whenever the field
scale and two field points are rational. Each can be discharged over an
entire interval by `quadratic_bernstein_pos_on`. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def fieldDX (p w : Point) : ℝ := w.1-p.1
def fieldDY (p w : Point) : ℝ := w.2-p.2

def QuadraticIntervalCert (A C D a b : ℝ) : Prop :=
  0 < quadraticAt A C D a ∧
  0 ≤ quadraticBernsteinMiddle A C D a b ∧
  0 < quadraticAt A C D b

theorem QuadraticIntervalCert.sound (A C D a b t : ℝ)
    (hab : a < b) (hat : a ≤ t) (htb : t ≤ b)
    (h : QuadraticIntervalCert A C D a b) :
    0 < quadraticAt A C D t :=
  quadratic_bernstein_pos_on A C D a b t hab hat htb h.1 h.2.1 h.2.2

def FieldCollisionCert (B : ℝ) (p w : Point) (a b : ℝ) : Prop :=
  QuadraticIntervalCert (B/2-fieldDX p w) (2*fieldDY p w)
    (B/2+fieldDX p w) a b ∧
  QuadraticIntervalCert (B/2+fieldDX p w) (-2*fieldDY p w)
    (B/2-fieldDX p w) a b ∧
  QuadraticIntervalCert (B/2-fieldDY p w) (-2*fieldDX p w)
    (B/2+fieldDY p w) a b ∧
  QuadraticIntervalCert (B/2+fieldDY p w) (2*fieldDX p w)
    (B/2-fieldDY p w) a b

theorem openSquare_of_field_quadratics (q : UnitSquare)
    (B : ℝ) (hB : 0 < B) (p w : Point) (t : ℝ)
    (hcenter : q.center = (p.1/B,p.2/B))
    (haxis : q.axis = chartAxis t)
    (hxlo : 0 < quadraticAt (B/2-fieldDX p w)
      (2*fieldDY p w) (B/2+fieldDX p w) t)
    (hxhi : 0 < quadraticAt (B/2+fieldDX p w)
      (-2*fieldDY p w) (B/2-fieldDX p w) t)
    (hylo : 0 < quadraticAt (B/2-fieldDY p w)
      (-2*fieldDX p w) (B/2+fieldDY p w) t)
    (hyhi : 0 < quadraticAt (B/2+fieldDY p w)
      (2*fieldDX p w) (B/2-fieldDY p w) t) :
    OpenSquare q (w.1/B,w.2/B) := by
  let dx := fieldDX p w
  let dy := fieldDY p w
  let den := B*(1+t^2)
  let nx := dx*(1-t^2)+2*dy*t
  let ny := dy*(1-t^2)-2*dx*t
  have hden : 0 < den := mul_pos hB (by positivity)
  have hxl : -(den/2) < nx := by
    dsimp [quadraticAt, den, nx, dx, dy] at hxlo ⊢
    nlinarith only [hxlo]
  have hxu : nx < den/2 := by
    dsimp [quadraticAt, den, nx, dx, dy] at hxhi ⊢
    nlinarith only [hxhi]
  have hyl : -(den/2) < ny := by
    dsimp [quadraticAt, den, ny, dx, dy] at hylo ⊢
    nlinarith only [hylo]
  have hyu : ny < den/2 := by
    dsimp [quadraticAt, den, ny, dx, dy] at hyhi ⊢
    nlinarith only [hyhi]
  have hX : localX q (w.1/B,w.2/B) = nx/den := by
    dsimp [localX, dot, nx, den, dx, dy, fieldDX, fieldDY]
    rw [hcenter, haxis]
    dsimp [chartAxis]
    have ht : 0 < 1+t^2 := by positivity
    field_simp [ne_of_gt hB, ne_of_gt ht]
    ring
  have hY : localY q (w.1/B,w.2/B) = ny/den := by
    dsimp [localY, dot, perp, ny, den, dx, dy, fieldDX, fieldDY]
    rw [hcenter, haxis]
    dsimp [chartAxis]
    have ht : 0 < 1+t^2 := by positivity
    field_simp [ne_of_gt hB, ne_of_gt ht]
    ring
  rw [OpenSquare, hX, hY]
  apply And.intro
  · apply abs_lt.mpr
    constructor
    · exact (lt_div_iff hden).mpr (by nlinarith only [hxl])
    · exact (div_lt_iff hden).mpr (by nlinarith only [hxu])
  · apply abs_lt.mpr
    constructor
    · exact (lt_div_iff hden).mpr (by nlinarith only [hyl])
    · exact (div_lt_iff hden).mpr (by nlinarith only [hyu])

/-- A proof producer supplies a single finite rational certificate for each
field vertex. The checker verifies four inequalities across every real angle
in the recorded closed interval, then converts to a physical unit square. -/
theorem FieldCollisionCert.sound (q : UnitSquare)
    (B : ℝ) (hB : 0 < B) (p w : Point) (a b t : ℝ)
    (hab : a < b) (hat : a ≤ t) (htb : t ≤ b)
    (hcenter : q.center = (p.1/B,p.2/B))
    (haxis : q.axis = chartAxis t)
    (hcert : FieldCollisionCert B p w a b) :
    OpenSquare q (w.1/B,w.2/B) := by
  rcases hcert with ⟨hxlo, hxhi, hylo, hyhi⟩
  exact openSquare_of_field_quadratics q B hB p w t hcenter haxis
    (hxlo.sound _ _ _ _ _ _ hab hat htb)
    (hxhi.sound _ _ _ _ _ _ hab hat htb)
    (hylo.sound _ _ _ _ _ _ hab hat htb)
    (hyhi.sound _ _ _ _ _ _ hab hat htb)

end
end ElevenSquare.Tasks.T07
