import ElevenSquare.Tasks.T07.LocalMinkowski
import ElevenSquare.Pending.Types

/-! A generic physical pose-row polygon obtained by pulling back an archived
field polygon. This one conversion removes per-row scale algebra from terminal
and ancestry certificates. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def fieldPullbackHalfplane (l : Halfplane) : Halfplane :=
  { a := l.a * fieldScaleRat, b := l.b * fieldScaleRat, c := l.c }

def fieldPullbackPolygon (P : Polygon) : Polygon :=
  P.map fieldPullbackHalfplane

theorem fieldPullbackHalfplane_iff (l : Halfplane) (p : Point) :
    (fieldPullbackHalfplane l).contains p ↔ l.contains (toField p) := by
  simp only [Halfplane.contains, fieldPullbackHalfplane, toField]
  rw [← fieldScaleRat_cast]
  push_cast
  constructor <;> intro h <;> convert h using 1 <;> ring

theorem fieldPullbackPolygon_iff (P : Polygon) (p : Point) :
    p ∈ (fieldPullbackPolygon P).carrier ↔ toField p ∈ P.carrier := by
  simp only [Polygon.carrier, Set.mem_setOf_eq, fieldPullbackPolygon,
    List.mem_map]
  constructor
  · intro hp l hl
    exact (fieldPullbackHalfplane_iff l p).mp
      (hp (fieldPullbackHalfplane l) ⟨l, hl, rfl⟩)
  · intro hp l hl
    obtain ⟨k, hk, rfl⟩ := hl
    exact (fieldPullbackHalfplane_iff k p).mpr (hp k hk)

def fieldPoseRow (lo hi : ℚ) (P : Polygon) : PoseRow :=
  { lo := lo, hi := hi, centers := fieldPullbackPolygon P }

theorem fieldPoseRow_source (lo hi : ℚ) (P : Polygon)
    (q : UnitSquare) (h : (fieldPoseRow lo hi P).contains q) :
    toField q.center ∈ P.carrier :=
  (fieldPullbackPolygon_iff P q.center).mp h.1

end
end ElevenSquare.Tasks.T07
