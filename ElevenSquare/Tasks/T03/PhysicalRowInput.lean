import ElevenSquare.Tasks.T03.ForwardRows
import ElevenSquare.Tasks.T03.AngleBands

namespace ElevenSquare.Pending.T03
noncomputable section

theorem AngleBand.wall_center (r : AngleBand) (h : r.check = true)
    (q : UnitSquare) (t : ℝ) (hc : ContainedAtCap q) (hq : q.axis=chartAxis t)
    (ht0 : (r.lo:ℝ) ≤ t) (ht1 : t ≤ (r.hi:ℝ)) :
    q.center ∈ IntegerCarrier (wallPlanes r.wallNum r.wallDen) := by
  obtain ⟨hd,hw,_,hab,_,ha,hb⟩ := of_decide_eq_true h
  have hw' : (0:ℝ) ≤ (r.width:ℝ) := by exact_mod_cast hw
  have hab' : (r.lo:ℝ) < (r.hi:ℝ) := by exact_mod_cast hab
  have ha' : (0:ℝ) ≤ 1-(r.width:ℝ)+2*(r.lo:ℝ)-(1+(r.width:ℝ))*(r.lo:ℝ)^2 := by
    exact_mod_cast ha
  have hb' : (0:ℝ) ≤ 1-(r.width:ℝ)+2*(r.hi:ℝ)-(1+(r.width:ℝ))*(r.hi:ℝ)^2 := by
    exact_mod_cast hb
  have hwall := contained_interval_wall_bounds q coverCap r.lo r.hi r.width t
    hc hq hw' hab' ht0 ht1 ha' hb'
  have he : (r.width:ℝ)/2 = (r.wallNum:ℝ)/r.wallDen := by
    simp [AngleBand.width]; ring
  rw [he] at hwall
  exact wallPlanes_of_bounds r.wallNum r.wallDen hd q.center
    hwall.1 hwall.2.1 hwall.2.2.1 hwall.2.2.2

structure PhysicalRowInput where
  band : AngleBand
  cuts : List SelfHullCutCertificate
  domain : List IntegerPlane
  implications : List LinearCertificate

def PhysicalRowInput.check (w : PhysicalRowInput) (r : IntegerRow) (vs : List QPoint) : Bool :=
  r.intervalCheck w.band.lo w.band.hi && w.band.check &&
  selfHullCutsCheck vs w.band.lo w.band.hi w.cuts &&
  planeImplicationsCheck (r.planes++w.cuts.map SelfHullCutCertificate.plane++
    wallPlanes w.band.wallNum w.band.wallDen) w.domain w.implications

theorem PhysicalRowInput.sound (w : PhysicalRowInput) (r : IntegerRow) (vs : List QPoint)
    (h : w.check r vs = true) (q : UnitSquare) (hq : r.row.contains q)
    (hc : ContainedAtCap q) (hold : rationalHull vs ⊆ {p | OpenSquare q p}) :
    q.center ∈ IntegerCarrier w.domain ∧
      ∃ t : ℝ, (w.band.lo:ℝ) ≤ t ∧ t ≤ (w.band.hi:ℝ) ∧ q.axis=chartAxis t := by
  simp only [check,Bool.and_eq_true] at h
  obtain ⟨t,ha,hb,haxis⟩ := r.interval_sound w.band.lo w.band.hi h.1.1.1 q hq
  have hcuts := selfHullCutsCheck_sound vs w.band.lo w.band.hi w.cuts h.1.2 q t haxis ha hb hold
  have hwalls := w.band.wall_center h.1.1.2 q t hc haxis ha hb
  have hp : q.center ∈ IntegerCarrier (r.planes++w.cuts.map SelfHullCutCertificate.plane++
      wallPlanes w.band.wallNum w.band.wallDen) := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · rcases List.mem_append.mp hl with hl | hl
      · exact r.center_mem q hq l hl
      · exact hcuts l hl
    · exact hwalls l hl
  exact ⟨planeImplicationsCheck_sound _ _ w.implications h.2 hp,t,ha,hb,haxis⟩

end
end ElevenSquare.Pending.T03
