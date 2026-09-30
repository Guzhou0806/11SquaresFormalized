import ElevenSquare.Tasks.T07.ShortcutFieldHull
import ElevenSquare.Tasks.T07.ShortcutCollisionChecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A generic row certificate: check each rational field vertex over the
entire rational angle interval, then convexity covers every source center. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem fieldHull_collision (q : UnitSquare)
    (vs : List QPoint) (w : QPoint) (a b : ℚ)
    (hc : toField q.center ∈ rationalHull vs)
    (ht : ∃ t : ℝ, (a : ℝ) ≤ t ∧ t ≤ (b : ℝ) ∧ q.axis = chartAxis t)
    (hab : a < b)
    (hvertices : ∀ v ∈ vs, FieldCollisionCert fieldScale
      (realPoint v) (realPoint w) (a : ℝ) (b : ℝ)) :
    OpenSquare q
      ((w.1 : ℝ)/fieldScale,(w.2 : ℝ)/fieldScale) := by
  obtain ⟨t, hta, htb, haxis⟩ := ht
  have hrealab : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  let W : Point := ((w.1 : ℝ)/fieldScale,(w.2 : ℝ)/fieldScale)
  have hphys := fieldHull_to_physicalHull vs hc
  change OpenSquare q W
  apply openSquare_of_center_hull q (vs.map physicalFieldVertex) W hphys
  intro v hv
  obtain ⟨v₀, hv₀, rfl⟩ := List.mem_map.mp hv
  let d : Point := ((realPoint w).1-(realPoint v₀).1,
    (realPoint w).2-(realPoint v₀).2)
  have hcert : FieldCollisionCert fieldScale (0,0) d a b := by
    simpa [FieldCollisionCert, fieldDX, fieldDY, d, realPoint] using
      hvertices v₀ hv₀
  have hinside := FieldCollisionCert.sound (recenteredSquare q)
    fieldScale fieldScale_pos (0,0) d a b t hrealab hta htb
    (by simp [recenteredSquare]) haxis hcert
  convert hinside using 1
  apply Prod.ext
  · dsimp [W, d, realPoint, physicalFieldVertex]
    push_cast
    rw [seedFieldScale_cast]
    field_simp [fieldScale_ne_zero] <;> ring
  · dsimp [W, d, realPoint, physicalFieldVertex]
    push_cast
    rw [seedFieldScale_cast]
    field_simp [fieldScale_ne_zero] <;> ring

end
end ElevenSquare.Tasks.T07
