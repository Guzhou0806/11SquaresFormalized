import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks9
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev79_planes : List IntegerPlane := integerOverlayPlanes ![6,5,10,13]
def rev79_plane6 : IntegerPlane := ⟨(-13084000000),(-2218132000000),(-623586975028)⟩
theorem rev79_plane6_mem : rev79_plane6 ∈ rev79_planes := by decide
def rev79_plane11 : IntegerPlane := ⟨2044968000000,(-643972000000),1318460524019⟩
theorem rev79_plane11_mem : rev79_plane11 ∈ rev79_planes := by decide
def rev79_plane28 : IntegerPlane := ⟨2144520000000,699568000000,1885510108648⟩
theorem rev79_plane28_mem : rev79_plane28 ∈ rev79_planes := by decide
def rev79_plane33 : IntegerPlane := ⟨51300000000,2168356000000,1004834835544⟩
theorem rev79_plane33_mem : rev79_plane33 ∈ rev79_planes := by decide
def rev79_plane73 : IntegerPlane := ⟨(-2218132000000),(-13084000000),(-1607629024972)⟩
theorem rev79_plane73_mem : rev79_plane73 ∈ rev79_planes := by decide
def rev79_vertex0 : FractionPoint := fractionRow79[0]!
theorem rev79_vertex0_mem : rev79_vertex0∈fractionRow79 := by decide
def rev79_vertex1 : FractionPoint := fractionRow79[1]!
theorem rev79_vertex1_mem : rev79_vertex1∈fractionRow79 := by decide
def rev79_vertex2 : FractionPoint := fractionRow79[2]!
theorem rev79_vertex2_mem : rev79_vertex2∈fractionRow79 := by decide
def rev79_vertex3 : FractionPoint := fractionRow79[3]!
theorem rev79_vertex3_mem : rev79_vertex3∈fractionRow79 := by decide
def rev79_vertex4 : FractionPoint := fractionRow79[4]!
theorem rev79_vertex4_mem : rev79_vertex4∈fractionRow79 := by decide
def rev79_s0_ll : FractionPoint := ⟨11423568365407659,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev79_s0_ll_mem : rev79_s0_ll.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane73 rev79_vertex4 rev79_vertex0 rev79_s0_ll
    rev79_vertex4_mem rev79_vertex0_mem (by decide)
def rev79_s0_lr : FractionPoint := ⟨132878752081,183754000000,50875247919,183754000000⟩
theorem rev79_s0_lr_mem : rev79_s0_lr.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane73 rev79_vertex4 rev79_vertex0 rev79_s0_lr
    rev79_vertex4_mem rev79_vertex0_mem (by decide)
def rev79_s0_ul : FractionPoint := ⟨11423568365407659,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev79_s0_ul_mem : rev79_s0_ul.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane33 rev79_vertex4 rev79_vertex3 rev79_s0_ul
    rev79_vertex4_mem rev79_vertex3_mem (by decide)
def rev79_s0_ur : FractionPoint := ⟨132878752081,183754000000,2339812373536801,5242685374000000⟩
theorem rev79_s0_ur_mem : rev79_s0_ur.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane33 rev79_vertex4 rev79_vertex3 rev79_s0_ur
    rev79_vertex4_mem rev79_vertex3_mem (by decide)
theorem rev79_slab0 (p : Point) (hp : p∈IntegerCarrier rev79_planes)
    (hx0 : rev79_s0_ll.real.1≤p.1) (hx1 : p.1≤rev79_s0_lr.real.1) :
    p∈rationalHull (fractionRow79.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev79_plane73 rev79_plane33 rev79_s0_ll rev79_s0_lr rev79_s0_ul rev79_s0_ur
    (by decide) rev79_s0_ll_mem rev79_s0_lr_mem rev79_s0_ul_mem rev79_s0_ur_mem p
    (hp _ rev79_plane73_mem) (hp _ rev79_plane33_mem) hx0 hx1
def rev79_s1_ll : FractionPoint := ⟨132878752081,183754000000,50875247919,183754000000⟩
theorem rev79_s1_ll_mem : rev79_s1_ll.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane6 rev79_vertex0 rev79_vertex1 rev79_s1_ll
    rev79_vertex0_mem rev79_vertex1_mem (by decide)
def rev79_s1_lr : FractionPoint := ⟨118789001090930133,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev79_s1_lr_mem : rev79_s1_lr.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane6 rev79_vertex0 rev79_vertex1 rev79_s1_lr
    rev79_vertex0_mem rev79_vertex1_mem (by decide)
def rev79_s1_ul : FractionPoint := ⟨132878752081,183754000000,2339812373536801,5242685374000000⟩
theorem rev79_s1_ul_mem : rev79_s1_ul.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane33 rev79_vertex4 rev79_vertex3 rev79_s1_ul
    rev79_vertex4_mem rev79_vertex3_mem (by decide)
def rev79_s1_ur : FractionPoint := ⟨118789001090930133,162301238908000000,2065685038825564714777,4630616647284148000000⟩
theorem rev79_s1_ur_mem : rev79_s1_ur.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane33 rev79_vertex4 rev79_vertex3 rev79_s1_ur
    rev79_vertex4_mem rev79_vertex3_mem (by decide)
theorem rev79_slab1 (p : Point) (hp : p∈IntegerCarrier rev79_planes)
    (hx0 : rev79_s1_ll.real.1≤p.1) (hx1 : p.1≤rev79_s1_lr.real.1) :
    p∈rationalHull (fractionRow79.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev79_plane6 rev79_plane33 rev79_s1_ll rev79_s1_lr rev79_s1_ul rev79_s1_ur
    (by decide) rev79_s1_ll_mem rev79_s1_lr_mem rev79_s1_ul_mem rev79_s1_ur_mem p
    (hp _ rev79_plane6_mem) (hp _ rev79_plane33_mem) hx0 hx1
def rev79_s2_ll : FractionPoint := ⟨118789001090930133,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev79_s2_ll_mem : rev79_s2_ll.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane11 rev79_vertex1 rev79_vertex2 rev79_s2_ll
    rev79_vertex1_mem rev79_vertex2_mem (by decide)
def rev79_s2_lr : FractionPoint := ⟨80699534251423,109987485000000,6671269350144029083,23609620230140000000⟩
theorem rev79_s2_lr_mem : rev79_s2_lr.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane11 rev79_vertex1 rev79_vertex2 rev79_s2_lr
    rev79_vertex1_mem rev79_vertex2_mem (by decide)
def rev79_s2_ul : FractionPoint := ⟨118789001090930133,162301238908000000,2065685038825564714777,4630616647284148000000⟩
theorem rev79_s2_ul_mem : rev79_s2_ul.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane33 rev79_vertex4 rev79_vertex3 rev79_s2_ul
    rev79_vertex4_mem rev79_vertex3_mem (by decide)
def rev79_s2_ur : FractionPoint := ⟨80699534251423,109987485000000,3270661284241,7332499000000⟩
theorem rev79_s2_ur_mem : rev79_s2_ur.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane33 rev79_vertex4 rev79_vertex3 rev79_s2_ur
    rev79_vertex4_mem rev79_vertex3_mem (by decide)
theorem rev79_slab2 (p : Point) (hp : p∈IntegerCarrier rev79_planes)
    (hx0 : rev79_s2_ll.real.1≤p.1) (hx1 : p.1≤rev79_s2_lr.real.1) :
    p∈rationalHull (fractionRow79.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev79_plane11 rev79_plane33 rev79_s2_ll rev79_s2_lr rev79_s2_ul rev79_s2_ur
    (by decide) rev79_s2_ll_mem rev79_s2_lr_mem rev79_s2_ul_mem rev79_s2_ur_mem p
    (hp _ rev79_plane11_mem) (hp _ rev79_plane33_mem) hx0 hx1
def rev79_s3_ll : FractionPoint := ⟨80699534251423,109987485000000,6671269350144029083,23609620230140000000⟩
theorem rev79_s3_ll_mem : rev79_s3_ll.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane11 rev79_vertex1 rev79_vertex2 rev79_s3_ll
    rev79_vertex1_mem rev79_vertex2_mem (by decide)
def rev79_s3_lr : FractionPoint := ⟨1935297561189487,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev79_s3_lr_mem : rev79_s3_lr.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane11 rev79_vertex1 rev79_vertex2 rev79_s3_lr
    rev79_vertex1_mem rev79_vertex2_mem (by decide)
def rev79_s3_ul : FractionPoint := ⟨80699534251423,109987485000000,3270661284241,7332499000000⟩
theorem rev79_s3_ul_mem : rev79_s3_ul.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane28 rev79_vertex3 rev79_vertex2 rev79_s3_ul
    rev79_vertex3_mem rev79_vertex2_mem (by decide)
def rev79_s3_ur : FractionPoint := ⟨1935297561189487,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev79_s3_ur_mem : rev79_s3_ur.real ∈ rationalHull (fractionRow79.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow79 rev79_plane28 rev79_vertex3 rev79_vertex2 rev79_s3_ur
    rev79_vertex3_mem rev79_vertex2_mem (by decide)
theorem rev79_slab3 (p : Point) (hp : p∈IntegerCarrier rev79_planes)
    (hx0 : rev79_s3_ll.real.1≤p.1) (hx1 : p.1≤rev79_s3_lr.real.1) :
    p∈rationalHull (fractionRow79.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev79_plane11 rev79_plane28 rev79_s3_ll rev79_s3_lr rev79_s3_ul rev79_s3_ur
    (by decide) rev79_s3_ll_mem rev79_s3_lr_mem rev79_s3_ul_mem rev79_s3_ur_mem p
    (hp _ rev79_plane11_mem) (hp _ rev79_plane28_mem) hx0 hx1
theorem rev79_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev79_planes) : rev79_s0_ll.real.1≤p.1 := by
  have hc := rev79_plane33.combine_sound rev79_plane73 13084000000 2168356000000 (by decide) (by decide) p
    (hp _ rev79_plane33_mem) (hp _ rev79_plane73_mem)
  exact (rev79_plane33.combine rev79_plane73 13084000000 2168356000000).xBoundCheck_sound rev79_s0_ll.nx rev79_s0_ll.dx true (by decide) p hc
theorem rev79_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev79_planes) : p.1≤rev79_s3_lr.real.1 := by
  have hc := rev79_plane11.combine_sound rev79_plane28 699568000000 643972000000 (by decide) (by decide) p
    (hp _ rev79_plane11_mem) (hp _ rev79_plane28_mem)
  exact (rev79_plane11.combine rev79_plane28 699568000000 643972000000).xBoundCheck_sound rev79_s3_lr.nx rev79_s3_lr.dx false (by decide) p hc
theorem rev79_hull (p : Point) (hp : p∈IntegerCarrier rev79_planes) :
    p∈rationalHull (fractionRow79.map FractionPoint.rational) := by
  have hxlo := rev79_bound0_lo p hp
  have hxhi := rev79_bound0_hi p hp
  by_cases h0 : p.1≤rev79_s0_lr.real.1
  · exact rev79_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev79_s1_lr.real.1
  · exact rev79_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev79_s2_lr.real.1
  · exact rev79_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev79_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull79 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,5,10,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow79 := by
  rw [← fractionRow79_correct]
  exact rev79_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull79
