import ElevenSquare.Tasks.T07.CapturePolygon
import ElevenSquare.Tasks.T07.CaptureSeedGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Source center polygons are in field coordinates. Scaling their exact
convex hulls back to physical unit-square coordinates is affine, so a finite
vertex collision check extends to every source center without sampling. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def physicalFieldVertex (v : QPoint) : QPoint :=
  (v.1/seedFieldScale, v.2/seedFieldScale)

def inverseFieldLinear : Point →ₗ[ℝ] Point where
  toFun p := (p.1/fieldScale,p.2/fieldScale)
  map_add' p q := by
    apply Prod.ext <;> dsimp [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' a p := by
    rcases p with ⟨x, y⟩
    apply Prod.ext <;> dsimp <;> ring

theorem inverseFieldLinear_realPoint (v : QPoint) :
    inverseFieldLinear (realPoint v) = realPoint (physicalFieldVertex v) := by
  apply Prod.ext
  · dsimp [inverseFieldLinear, realPoint, physicalFieldVertex]
    push_cast
    rw [seedFieldScale_cast]
  · dsimp [inverseFieldLinear, realPoint, physicalFieldVertex]
    push_cast
    rw [seedFieldScale_cast]

theorem inverseFieldLinear_toField (p : Point) :
    inverseFieldLinear (toField p) = p := by
  apply Prod.ext <;>
    dsimp [inverseFieldLinear, toField] <;>
    field_simp [fieldScale_ne_zero] <;> ring

theorem fieldHull_to_physicalHull (vs : List QPoint) {p : Point}
    (hp : toField p ∈ rationalHull vs) :
    p ∈ rationalHull (vs.map physicalFieldVertex) := by
  let base : Set Point := {x | ∃ v ∈ vs, x = realPoint v}
  let scaled : Set Point :=
    {x | ∃ v ∈ vs.map physicalFieldVertex, x = realPoint v}
  have hbase : inverseFieldLinear '' base = scaled := by
    ext x
    constructor
    · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨physicalFieldVertex v, List.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
      exact inverseFieldLinear_realPoint v
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
      exact ⟨realPoint v, ⟨v, hv, rfl⟩,
        inverseFieldLinear_realPoint v⟩
  have himage := inverseFieldLinear.image_convexHull base
  have hmem : inverseFieldLinear (toField p) ∈
      inverseFieldLinear '' (convexHull ℝ base) :=
    ⟨toField p, hp, rfl⟩
  rw [himage, hbase] at hmem
  rw [inverseFieldLinear_toField] at hmem
  exact hmem

end
end ElevenSquare.Tasks.T07
