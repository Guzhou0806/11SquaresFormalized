import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks23
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev184_planes : List IntegerPlane := integerOverlayPlanes ![12,15,0,3]
def rev184_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev184_plane0_mem : rev184_plane0 ∈ rev184_planes := by decide
def rev184_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev184_plane3_mem : rev184_plane3 ∈ rev184_planes := by decide
def rev184_plane12 : IntegerPlane := ⟨(-202532000000),(-1861776000000),(-1478404260553)⟩
theorem rev184_plane12_mem : rev184_plane12 ∈ rev184_planes := by decide
def rev184_plane71 : IntegerPlane := ⟨1861776000000,202532000000,585903739447⟩
theorem rev184_plane71_mem : rev184_plane71 ∈ rev184_planes := by decide
def rev184_vertex0 : FractionPoint := fractionRow184[0]!
theorem rev184_vertex0_mem : rev184_vertex0∈fractionRow184 := by decide
def rev184_vertex1 : FractionPoint := fractionRow184[1]!
theorem rev184_vertex1_mem : rev184_vertex1∈fractionRow184 := by decide
def rev184_vertex2 : FractionPoint := fractionRow184[2]!
theorem rev184_vertex2_mem : rev184_vertex2∈fractionRow184 := by decide
def rev184_vertex3 : FractionPoint := fractionRow184[3]!
theorem rev184_vertex3_mem : rev184_vertex3∈fractionRow184 := by decide
def rev184_s0_ll : FractionPoint := ⟨0,1,1478404260553,1861776000000⟩
theorem rev184_s0_ll_mem : rev184_s0_ll.real ∈ rationalHull (fractionRow184.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow184 rev184_plane12 rev184_vertex2 rev184_vertex3 rev184_s0_ll
    rev184_vertex2_mem rev184_vertex3_mem (by decide)
def rev184_s0_lr : FractionPoint := ⟨383371739447,1861776000000,668703131365410581,866552468544000000⟩
theorem rev184_s0_lr_mem : rev184_s0_lr.real ∈ rationalHull (fractionRow184.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow184 rev184_plane12 rev184_vertex2 rev184_vertex3 rev184_s0_lr
    rev184_vertex2_mem rev184_vertex3_mem (by decide)
def rev184_s0_ul : FractionPoint := ⟨0,1,1,1⟩
theorem rev184_s0_ul_mem : rev184_s0_ul.real ∈ rationalHull (fractionRow184.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow184 rev184_plane3 rev184_vertex1 rev184_vertex0 rev184_s0_ul
    rev184_vertex1_mem rev184_vertex0_mem (by decide)
def rev184_s0_ur : FractionPoint := ⟨383371739447,1861776000000,1,1⟩
theorem rev184_s0_ur_mem : rev184_s0_ur.real ∈ rationalHull (fractionRow184.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow184 rev184_plane3 rev184_vertex1 rev184_vertex0 rev184_s0_ur
    rev184_vertex1_mem rev184_vertex0_mem (by decide)
theorem rev184_slab0 (p : Point) (hp : p∈IntegerCarrier rev184_planes)
    (hx0 : rev184_s0_ll.real.1≤p.1) (hx1 : p.1≤rev184_s0_lr.real.1) :
    p∈rationalHull (fractionRow184.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev184_plane12 rev184_plane3 rev184_s0_ll rev184_s0_lr rev184_s0_ul rev184_s0_ur
    (by decide) rev184_s0_ll_mem rev184_s0_lr_mem rev184_s0_ul_mem rev184_s0_ur_mem p
    (hp _ rev184_plane12_mem) (hp _ rev184_plane3_mem) hx0 hx1
def rev184_s1_ll : FractionPoint := ⟨383371739447,1861776000000,668703131365410581,866552468544000000⟩
theorem rev184_s1_ll_mem : rev184_s1_ll.real ∈ rationalHull (fractionRow184.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow184 rev184_plane12 rev184_vertex2 rev184_vertex3 rev184_s1_ll
    rev184_vertex2_mem rev184_vertex3_mem (by decide)
def rev184_s1_lr : FractionPoint := ⟨383371739447,1659244000000,1275872260553,1659244000000⟩
theorem rev184_s1_lr_mem : rev184_s1_lr.real ∈ rationalHull (fractionRow184.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow184 rev184_plane12 rev184_vertex2 rev184_vertex3 rev184_s1_lr
    rev184_vertex2_mem rev184_vertex3_mem (by decide)
def rev184_s1_ul : FractionPoint := ⟨383371739447,1861776000000,1,1⟩
theorem rev184_s1_ul_mem : rev184_s1_ul.real ∈ rationalHull (fractionRow184.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow184 rev184_plane71 rev184_vertex0 rev184_vertex3 rev184_s1_ul
    rev184_vertex0_mem rev184_vertex3_mem (by decide)
def rev184_s1_ur : FractionPoint := ⟨383371739447,1659244000000,1275872260553,1659244000000⟩
theorem rev184_s1_ur_mem : rev184_s1_ur.real ∈ rationalHull (fractionRow184.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow184 rev184_plane71 rev184_vertex0 rev184_vertex3 rev184_s1_ur
    rev184_vertex0_mem rev184_vertex3_mem (by decide)
theorem rev184_slab1 (p : Point) (hp : p∈IntegerCarrier rev184_planes)
    (hx0 : rev184_s1_ll.real.1≤p.1) (hx1 : p.1≤rev184_s1_lr.real.1) :
    p∈rationalHull (fractionRow184.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev184_plane12 rev184_plane71 rev184_s1_ll rev184_s1_lr rev184_s1_ul rev184_s1_ur
    (by decide) rev184_s1_ll_mem rev184_s1_lr_mem rev184_s1_ul_mem rev184_s1_ur_mem p
    (hp _ rev184_plane12_mem) (hp _ rev184_plane71_mem) hx0 hx1
theorem rev184_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev184_planes) : rev184_s0_ll.real.1≤p.1 := by
  have hc := rev184_plane0.combine_sound rev184_plane0 1 0 (by decide) (by decide) p
    (hp _ rev184_plane0_mem) (hp _ rev184_plane0_mem)
  exact (rev184_plane0.combine rev184_plane0 1 0).xBoundCheck_sound rev184_s0_ll.nx rev184_s0_ll.dx true (by decide) p hc
theorem rev184_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev184_planes) : p.1≤rev184_s1_lr.real.1 := by
  have hc := rev184_plane12.combine_sound rev184_plane71 202532000000 1861776000000 (by decide) (by decide) p
    (hp _ rev184_plane12_mem) (hp _ rev184_plane71_mem)
  exact (rev184_plane12.combine rev184_plane71 202532000000 1861776000000).xBoundCheck_sound rev184_s1_lr.nx rev184_s1_lr.dx false (by decide) p hc
theorem rev184_hull (p : Point) (hp : p∈IntegerCarrier rev184_planes) :
    p∈rationalHull (fractionRow184.map FractionPoint.rational) := by
  have hxlo := rev184_bound0_lo p hp
  have hxhi := rev184_bound0_hi p hp
  by_cases h0 : p.1≤rev184_s0_lr.real.1
  · exact rev184_slab0 p hp hxlo h0
  exact rev184_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull184 (p : Point)
    (hp : ∀ g, ClosedCell ((![12,15,0,3] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow184 := by
  rw [← fractionRow184_correct]
  exact rev184_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull184
