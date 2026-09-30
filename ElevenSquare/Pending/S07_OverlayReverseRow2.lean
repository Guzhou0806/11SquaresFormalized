import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks0
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev2_planes : List IntegerPlane := integerOverlayPlanes ![0,3,3,0]
def rev2_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev2_plane0_mem : rev2_plane0 ∈ rev2_planes := by decide
def rev2_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev2_plane2_mem : rev2_plane2 ∈ rev2_planes := by decide
def rev2_plane31 : IntegerPlane := ⟨(-202532000000),1861776000000,383371739447⟩
theorem rev2_plane31_mem : rev2_plane31 ∈ rev2_planes := by decide
def rev2_plane51 : IntegerPlane := ⟨1861776000000,(-202532000000),383371739447⟩
theorem rev2_plane51_mem : rev2_plane51 ∈ rev2_planes := by decide
def rev2_vertex0 : FractionPoint := fractionRow2[0]!
theorem rev2_vertex0_mem : rev2_vertex0∈fractionRow2 := by decide
def rev2_vertex1 : FractionPoint := fractionRow2[1]!
theorem rev2_vertex1_mem : rev2_vertex1∈fractionRow2 := by decide
def rev2_vertex2 : FractionPoint := fractionRow2[2]!
theorem rev2_vertex2_mem : rev2_vertex2∈fractionRow2 := by decide
def rev2_vertex3 : FractionPoint := fractionRow2[3]!
theorem rev2_vertex3_mem : rev2_vertex3∈fractionRow2 := by decide
def rev2_s0_ll : FractionPoint := ⟨0,1,0,1⟩
theorem rev2_s0_ll_mem : rev2_s0_ll.real ∈ rationalHull (fractionRow2.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow2 rev2_plane2 rev2_vertex0 rev2_vertex1 rev2_s0_ll
    rev2_vertex0_mem rev2_vertex1_mem (by decide)
def rev2_s0_lr : FractionPoint := ⟨383371739447,1861776000000,0,1⟩
theorem rev2_s0_lr_mem : rev2_s0_lr.real ∈ rationalHull (fractionRow2.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow2 rev2_plane2 rev2_vertex0 rev2_vertex1 rev2_s0_lr
    rev2_vertex0_mem rev2_vertex1_mem (by decide)
def rev2_s0_ul : FractionPoint := ⟨0,1,383371739447,1861776000000⟩
theorem rev2_s0_ul_mem : rev2_s0_ul.real ∈ rationalHull (fractionRow2.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow2 rev2_plane31 rev2_vertex3 rev2_vertex2 rev2_s0_ul
    rev2_vertex3_mem rev2_vertex2_mem (by decide)
def rev2_s0_ur : FractionPoint := ⟨383371739447,1861776000000,197849337178589419,866552468544000000⟩
theorem rev2_s0_ur_mem : rev2_s0_ur.real ∈ rationalHull (fractionRow2.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow2 rev2_plane31 rev2_vertex3 rev2_vertex2 rev2_s0_ur
    rev2_vertex3_mem rev2_vertex2_mem (by decide)
theorem rev2_slab0 (p : Point) (hp : p∈IntegerCarrier rev2_planes)
    (hx0 : rev2_s0_ll.real.1≤p.1) (hx1 : p.1≤rev2_s0_lr.real.1) :
    p∈rationalHull (fractionRow2.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev2_plane2 rev2_plane31 rev2_s0_ll rev2_s0_lr rev2_s0_ul rev2_s0_ur
    (by decide) rev2_s0_ll_mem rev2_s0_lr_mem rev2_s0_ul_mem rev2_s0_ur_mem p
    (hp _ rev2_plane2_mem) (hp _ rev2_plane31_mem) hx0 hx1
def rev2_s1_ll : FractionPoint := ⟨383371739447,1861776000000,0,1⟩
theorem rev2_s1_ll_mem : rev2_s1_ll.real ∈ rationalHull (fractionRow2.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow2 rev2_plane51 rev2_vertex1 rev2_vertex2 rev2_s1_ll
    rev2_vertex1_mem rev2_vertex2_mem (by decide)
def rev2_s1_lr : FractionPoint := ⟨383371739447,1659244000000,383371739447,1659244000000⟩
theorem rev2_s1_lr_mem : rev2_s1_lr.real ∈ rationalHull (fractionRow2.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow2 rev2_plane51 rev2_vertex1 rev2_vertex2 rev2_s1_lr
    rev2_vertex1_mem rev2_vertex2_mem (by decide)
def rev2_s1_ul : FractionPoint := ⟨383371739447,1861776000000,197849337178589419,866552468544000000⟩
theorem rev2_s1_ul_mem : rev2_s1_ul.real ∈ rationalHull (fractionRow2.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow2 rev2_plane31 rev2_vertex3 rev2_vertex2 rev2_s1_ul
    rev2_vertex3_mem rev2_vertex2_mem (by decide)
def rev2_s1_ur : FractionPoint := ⟨383371739447,1659244000000,383371739447,1659244000000⟩
theorem rev2_s1_ur_mem : rev2_s1_ur.real ∈ rationalHull (fractionRow2.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow2 rev2_plane31 rev2_vertex3 rev2_vertex2 rev2_s1_ur
    rev2_vertex3_mem rev2_vertex2_mem (by decide)
theorem rev2_slab1 (p : Point) (hp : p∈IntegerCarrier rev2_planes)
    (hx0 : rev2_s1_ll.real.1≤p.1) (hx1 : p.1≤rev2_s1_lr.real.1) :
    p∈rationalHull (fractionRow2.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev2_plane51 rev2_plane31 rev2_s1_ll rev2_s1_lr rev2_s1_ul rev2_s1_ur
    (by decide) rev2_s1_ll_mem rev2_s1_lr_mem rev2_s1_ul_mem rev2_s1_ur_mem p
    (hp _ rev2_plane51_mem) (hp _ rev2_plane31_mem) hx0 hx1
theorem rev2_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev2_planes) : rev2_s0_ll.real.1≤p.1 := by
  have hc := rev2_plane0.combine_sound rev2_plane0 1 0 (by decide) (by decide) p
    (hp _ rev2_plane0_mem) (hp _ rev2_plane0_mem)
  exact (rev2_plane0.combine rev2_plane0 1 0).xBoundCheck_sound rev2_s0_ll.nx rev2_s0_ll.dx true (by decide) p hc
theorem rev2_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev2_planes) : p.1≤rev2_s1_lr.real.1 := by
  have hc := rev2_plane31.combine_sound rev2_plane51 202532000000 1861776000000 (by decide) (by decide) p
    (hp _ rev2_plane31_mem) (hp _ rev2_plane51_mem)
  exact (rev2_plane31.combine rev2_plane51 202532000000 1861776000000).xBoundCheck_sound rev2_s1_lr.nx rev2_s1_lr.dx false (by decide) p hc
theorem rev2_hull (p : Point) (hp : p∈IntegerCarrier rev2_planes) :
    p∈rationalHull (fractionRow2.map FractionPoint.rational) := by
  have hxlo := rev2_bound0_lo p hp
  have hxhi := rev2_bound0_hi p hp
  by_cases h0 : p.1≤rev2_s0_lr.real.1
  · exact rev2_slab0 p hp hxlo h0
  exact rev2_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull2 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,3,3,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow2 := by
  rw [← fractionRow2_correct]
  exact rev2_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull2
