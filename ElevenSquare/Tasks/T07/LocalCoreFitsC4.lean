import ElevenSquare.Tasks.T07.LocalCoreFitsQuadratic
import ElevenSquare.Pending.S05_OwnedHull

/-! A quarter turn preserves the two strict local-coordinate inequalities.
One strict radial bound handles a seed independently of square orientation. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def rotateQ (v : QPoint) : QPoint := (-v.2, v.1)

def coreOrbitVertices (u v : QPoint) : List QPoint :=
  [u, v, rotateQ u, rotateQ v, rotateQ (rotateQ u),
   rotateQ (rotateQ v), rotateQ (rotateQ (rotateQ u)),
   rotateQ (rotateQ (rotateQ v))]

theorem normalized_rotateQ (v : QPoint) :
    realPoint (qpointFieldNormalize (rotateQ v)) =
      perp (realPoint (qpointFieldNormalize v)) := by
  apply Prod.ext <;> simp [rotateQ, qpointFieldNormalize, realPoint, perp, neg_div]

theorem core_offset_open_rotate (q : UnitSquare) (v : Point)
    (hv : OpenSquare q (q.center + v)) :
    OpenSquare q (q.center + perp v) := by
  have hx : localX q (q.center + perp v) =
      -localY q (q.center + v) := by
    dsimp [localX, localY, dot, perp]
    ring
  have hy : localY q (q.center + perp v) =
      localX q (q.center + v) := by
    dsimp [localX, localY, dot, perp]
    ring
  rw [OpenSquare, hx, hy]
  exact ⟨by simpa only [abs_neg] using hv.2, hv.1⟩

theorem normalized_core_open_rotate (q : UnitSquare) (v : QPoint)
    (hv : OpenSquare q (q.center + realPoint (qpointFieldNormalize v))) :
    OpenSquare q (q.center + realPoint (qpointFieldNormalize (rotateQ v))) := by
  rw [normalized_rotateQ]
  exact core_offset_open_rotate q _ hv

theorem core_offset_open_of_normSq_lt (q : UnitSquare) (v : Point)
    (hv : normSq v < 1/4) : OpenSquare q (q.center + v) := by
  apply open_of_normSq_lt
  simpa only [add_sub_cancel_left] using hv

theorem normalized_core_open_of_normSq_lt (q : UnitSquare) (v : QPoint)
    (hv : normSq (realPoint (qpointFieldNormalize v)) < 1/4) :
    OpenSquare q (q.center + realPoint (qpointFieldNormalize v)) :=
  core_offset_open_of_normSq_lt q _ hv

/-- Two strict seed vertices imply the whole eight-vertex rational core hull
fits in every actual physical unit square with this orientation. -/
theorem coreOrbit_coreFits (q : UnitSquare) (u v : QPoint)
    (hu : OpenSquare q (q.center + realPoint (qpointFieldNormalize u)))
    (hv : OpenSquare q (q.center + realPoint (qpointFieldNormalize v))) :
    CoreFits (rationalHull ((coreOrbitVertices u v).map qpointFieldNormalize)) q := by
  have hu1 := normalized_core_open_rotate q u hu
  have hv1 := normalized_core_open_rotate q v hv
  have hu2 := normalized_core_open_rotate q (rotateQ u) hu1
  have hv2 := normalized_core_open_rotate q (rotateQ v) hv1
  have hu3 := normalized_core_open_rotate q (rotateQ (rotateQ u)) hu2
  have hv3 := normalized_core_open_rotate q (rotateQ (rotateQ v)) hv2
  apply common_core_hull
  intro w hw
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
  simp only [coreOrbitVertices, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hu
  · exact hv
  · exact hu1
  · exact hv1
  · exact hu2
  · exact hv2
  · exact hu3
  · exact hv3

end
end ElevenSquare.Tasks.T07
