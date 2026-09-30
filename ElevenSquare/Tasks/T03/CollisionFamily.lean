import ElevenSquare.Tasks.T03.CollisionRows
import ElevenSquare.Tasks.T03.HomogeneousSupport

namespace ElevenSquare.Pending.T03
noncomputable section

structure PartnerBand where
  row : PoseRow
  centers : List HomPoint
  core : List QPoint
  sound : ∀ r, row.contains r →
    r.center ∈ rationalHull (centers.map HomPoint.point) ∧ CoreFits (rationalHull core) r

structure CollisionBandSupport (qi : List QPoint) (xs : List HomPoint) (band : PartnerBand) where
  planes : List IntegerPlane
  supports : List DifferenceSupport
  contained : IntegerCarrier planes ⊆ forbiddenCenters (rationalHull band.core) (rationalHull qi)
  checked : homSupportCheck xs band.centers planes supports = true

theorem CollisionBandSupport.sound {qi : List QPoint} {xs : List HomPoint} {band : PartnerBand}
    (w : CollisionBandSupport qi xs band) (q r : UnitSquare)
    (hq : CoreFits (rationalHull qi) q) (hx : q.center ∈ rationalHull (xs.map HomPoint.point))
    (hr : band.row.contains r) : ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  obtain ⟨hy,hj⟩ := band.sound r hr
  exact core_difference_overlap q r _ _ hq hj
    (w.contained (homSupportCheck_sound xs band.centers w.planes w.supports w.checked
      q.center hx r.center hy))

structure CollisionBand (qi : List QPoint) (xs : List HomPoint) where
  row : PoseRow
  collision : ∀ q r, CoreFits (rationalHull qi) q →
    q.center ∈ rationalHull (xs.map HomPoint.point) → row.contains r →
    ∃ p, OpenSquare q p ∧ OpenSquare r p

def CollisionBand.ofSupport {qi : List QPoint} {xs : List HomPoint} {band : PartnerBand}
    (w : CollisionBandSupport qi xs band) : CollisionBand qi xs where
  row := band.row
  collision := w.sound

def CollisionBand.impossible (qi : List QPoint) (xs : List HomPoint) (row : PoseRow)
    (h : ∀ r, ¬ row.contains r) : CollisionBand qi xs where
  row := row
  collision := by
    intro q r hq hx hr
    exact False.elim (h r hr)

def CollisionBand.rows {qi : List QPoint} {xs : List HomPoint}
    (bands : List (CollisionBand qi xs)) : List PoseRow := bands.map CollisionBand.row

theorem CollisionBand.universal {qi : List QPoint} {xs : List HomPoint}
    (bands : List (CollisionBand qi xs)) (q r : UnitSquare)
    (hq : CoreFits (rationalHull qi) q) (hx : q.center ∈ rationalHull (xs.map HomPoint.point))
    (hr : RowsContain (CollisionBand.rows bands) r) :
    ∃ p, OpenSquare q p ∧ OpenSquare r p := by
  obtain ⟨row,hrow,hr⟩ := hr
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hrow
  exact w.collision q r hq hx hr

end
end ElevenSquare.Pending.T03
