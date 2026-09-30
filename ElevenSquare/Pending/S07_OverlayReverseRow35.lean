import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks4
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev35_planes : List IntegerPlane := integerOverlayPlanes ![3,0,15,12]
def rev35_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev35_plane1_mem : rev35_plane1 ∈ rev35_planes := by decide
def rev35_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev35_plane2_mem : rev35_plane2 ∈ rev35_planes := by decide
def rev35_plane11 : IntegerPlane := ⟨202532000000,1861776000000,585903739447⟩
theorem rev35_plane11_mem : rev35_plane11 ∈ rev35_planes := by decide
def rev35_plane72 : IntegerPlane := ⟨(-1861776000000),(-202532000000),(-1478404260553)⟩
theorem rev35_plane72_mem : rev35_plane72 ∈ rev35_planes := by decide
def rev35_vertex0 : FractionPoint := fractionRow35[0]!
theorem rev35_vertex0_mem : rev35_vertex0∈fractionRow35 := by decide
def rev35_vertex1 : FractionPoint := fractionRow35[1]!
theorem rev35_vertex1_mem : rev35_vertex1∈fractionRow35 := by decide
def rev35_vertex2 : FractionPoint := fractionRow35[2]!
theorem rev35_vertex2_mem : rev35_vertex2∈fractionRow35 := by decide
def rev35_vertex3 : FractionPoint := fractionRow35[3]!
theorem rev35_vertex3_mem : rev35_vertex3∈fractionRow35 := by decide
def rev35_s0_ll : FractionPoint := ⟨1275872260553,1659244000000,383371739447,1659244000000⟩
theorem rev35_s0_ll_mem : rev35_s0_ll.real ∈ rationalHull (fractionRow35.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow35 rev35_plane72 rev35_vertex3 rev35_vertex0 rev35_s0_ll
    rev35_vertex3_mem rev35_vertex0_mem (by decide)
def rev35_s0_lr : FractionPoint := ⟨1478404260553,1861776000000,0,1⟩
theorem rev35_s0_lr_mem : rev35_s0_lr.real ∈ rationalHull (fractionRow35.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow35 rev35_plane72 rev35_vertex3 rev35_vertex0 rev35_s0_lr
    rev35_vertex3_mem rev35_vertex0_mem (by decide)
def rev35_s0_ul : FractionPoint := ⟨1275872260553,1659244000000,383371739447,1659244000000⟩
theorem rev35_s0_ul_mem : rev35_s0_ul.real ∈ rationalHull (fractionRow35.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow35 rev35_plane11 rev35_vertex3 rev35_vertex2 rev35_s0_ul
    rev35_vertex3_mem rev35_vertex2_mem (by decide)
def rev35_s0_ur : FractionPoint := ⟨1478404260553,1861776000000,197849337178589419,866552468544000000⟩
theorem rev35_s0_ur_mem : rev35_s0_ur.real ∈ rationalHull (fractionRow35.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow35 rev35_plane11 rev35_vertex3 rev35_vertex2 rev35_s0_ur
    rev35_vertex3_mem rev35_vertex2_mem (by decide)
theorem rev35_slab0 (p : Point) (hp : p∈IntegerCarrier rev35_planes)
    (hx0 : rev35_s0_ll.real.1≤p.1) (hx1 : p.1≤rev35_s0_lr.real.1) :
    p∈rationalHull (fractionRow35.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev35_plane72 rev35_plane11 rev35_s0_ll rev35_s0_lr rev35_s0_ul rev35_s0_ur
    (by decide) rev35_s0_ll_mem rev35_s0_lr_mem rev35_s0_ul_mem rev35_s0_ur_mem p
    (hp _ rev35_plane72_mem) (hp _ rev35_plane11_mem) hx0 hx1
def rev35_s1_ll : FractionPoint := ⟨1478404260553,1861776000000,0,1⟩
theorem rev35_s1_ll_mem : rev35_s1_ll.real ∈ rationalHull (fractionRow35.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow35 rev35_plane2 rev35_vertex0 rev35_vertex1 rev35_s1_ll
    rev35_vertex0_mem rev35_vertex1_mem (by decide)
def rev35_s1_lr : FractionPoint := ⟨1,1,0,1⟩
theorem rev35_s1_lr_mem : rev35_s1_lr.real ∈ rationalHull (fractionRow35.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow35 rev35_plane2 rev35_vertex0 rev35_vertex1 rev35_s1_lr
    rev35_vertex0_mem rev35_vertex1_mem (by decide)
def rev35_s1_ul : FractionPoint := ⟨1478404260553,1861776000000,197849337178589419,866552468544000000⟩
theorem rev35_s1_ul_mem : rev35_s1_ul.real ∈ rationalHull (fractionRow35.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow35 rev35_plane11 rev35_vertex3 rev35_vertex2 rev35_s1_ul
    rev35_vertex3_mem rev35_vertex2_mem (by decide)
def rev35_s1_ur : FractionPoint := ⟨1,1,383371739447,1861776000000⟩
theorem rev35_s1_ur_mem : rev35_s1_ur.real ∈ rationalHull (fractionRow35.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow35 rev35_plane11 rev35_vertex3 rev35_vertex2 rev35_s1_ur
    rev35_vertex3_mem rev35_vertex2_mem (by decide)
theorem rev35_slab1 (p : Point) (hp : p∈IntegerCarrier rev35_planes)
    (hx0 : rev35_s1_ll.real.1≤p.1) (hx1 : p.1≤rev35_s1_lr.real.1) :
    p∈rationalHull (fractionRow35.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev35_plane2 rev35_plane11 rev35_s1_ll rev35_s1_lr rev35_s1_ul rev35_s1_ur
    (by decide) rev35_s1_ll_mem rev35_s1_lr_mem rev35_s1_ul_mem rev35_s1_ur_mem p
    (hp _ rev35_plane2_mem) (hp _ rev35_plane11_mem) hx0 hx1
theorem rev35_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev35_planes) : rev35_s0_ll.real.1≤p.1 := by
  have hc := rev35_plane11.combine_sound rev35_plane72 202532000000 1861776000000 (by decide) (by decide) p
    (hp _ rev35_plane11_mem) (hp _ rev35_plane72_mem)
  exact (rev35_plane11.combine rev35_plane72 202532000000 1861776000000).xBoundCheck_sound rev35_s0_ll.nx rev35_s0_ll.dx true (by decide) p hc
theorem rev35_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev35_planes) : p.1≤rev35_s1_lr.real.1 := by
  have hc := rev35_plane1.combine_sound rev35_plane1 1 0 (by decide) (by decide) p
    (hp _ rev35_plane1_mem) (hp _ rev35_plane1_mem)
  exact (rev35_plane1.combine rev35_plane1 1 0).xBoundCheck_sound rev35_s1_lr.nx rev35_s1_lr.dx false (by decide) p hc
theorem rev35_hull (p : Point) (hp : p∈IntegerCarrier rev35_planes) :
    p∈rationalHull (fractionRow35.map FractionPoint.rational) := by
  have hxlo := rev35_bound0_lo p hp
  have hxhi := rev35_bound0_hi p hp
  by_cases h0 : p.1≤rev35_s0_lr.real.1
  · exact rev35_slab0 p hp hxlo h0
  exact rev35_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull35 (p : Point)
    (hp : ∀ g, ClosedCell ((![3,0,15,12] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow35 := by
  rw [← fractionRow35_correct]
  exact rev35_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull35
