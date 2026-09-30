import ElevenSquare.Pending.S07_FractionOrder
import ElevenSquare.Pending.S07_SegmentWitness
namespace ElevenSquare.Pending

def edgePointCheck (l : IntegerPlane) (p q z : FractionPoint) : Bool :=
  decide (l.b≠0 ∧ fractionLT p.nx p.dx q.nx q.dx=true ∧
    fractionLE p.nx p.dx z.nx z.dx=true ∧ fractionLE z.nx z.dx q.nx q.dx=true ∧
    p.onPlaneCheck l=true ∧ q.onPlaneCheck l=true ∧ z.onPlaneCheck l=true)

theorem edgePointCheck_sound {C : Set Point} (hc : Convex ℝ C)
    (l : IntegerPlane) (p q z : FractionPoint) (h : edgePointCheck l p q z = true)
    (hp : p.real∈C) (hq : q.real∈C) : z.real∈C := by
  obtain ⟨hb, hw, hl, hr, hpLine, hqLine, hzLine⟩ := of_decide_eq_true h
  have hb' : (l.b:ℝ)≠0 := by exact_mod_cast hb
  have hpl := p.onPlaneCheck_sound l hpLine
  have hql := q.onPlaneCheck_sound l hqLine
  have hzl := z.onPlaneCheck_sound l hzLine
  rw [← p.real_correct] at hpl
  rw [← q.real_correct] at hql
  rw [← z.real_correct] at hzl
  exact convex_point_on_edge hc l.a l.b l.c p.real.1 q.real.1 p.real.2 q.real.2
    z.real.1 z.real.2 hb' (p.xLT q hw) (p.xLE z hl) (z.xLE q hr) hp hq hpl hql hzl

theorem FractionPoint.mem_rationalHull (qs : List FractionPoint) (q : FractionPoint)
    (h : q ∈ qs) : q.real ∈ rationalHull (qs.map FractionPoint.rational) := by
  rw [q.real_correct]
  exact subset_convexHull ℝ _ ⟨q.rational, List.mem_map.mpr ⟨q,h,rfl⟩,rfl⟩

theorem edgePointCheck_hull (qs : List FractionPoint) (l : IntegerPlane)
    (p q z : FractionPoint) (hp : p∈qs) (hq : q∈qs)
    (h : edgePointCheck l p q z = true) :
    z.real ∈ rationalHull (qs.map FractionPoint.rational) :=
  edgePointCheck_sound (convex_convexHull ℝ _) l p q z h
    (p.mem_rationalHull qs hp) (q.mem_rationalHull qs hq)

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.edgePointCheck_hull
