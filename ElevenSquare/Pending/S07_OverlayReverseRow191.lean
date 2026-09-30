import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks23
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev191_planes : List IntegerPlane := integerOverlayPlanes ![13,10,5,6]
def rev191_plane13 : IntegerPlane := ⟨(-13084000000),(-2218132000000),(-1607629024972)⟩
theorem rev191_plane13_mem : rev191_plane13 ∈ rev191_planes := by decide
def rev191_plane48 : IntegerPlane := ⟨699568000000,2144520000000,1885510108648⟩
theorem rev191_plane48_mem : rev191_plane48 ∈ rev191_planes := by decide
def rev191_plane53 : IntegerPlane := ⟨2168356000000,51300000000,1004834835544⟩
theorem rev191_plane53_mem : rev191_plane53 ∈ rev191_planes := by decide
def rev191_plane66 : IntegerPlane := ⟨(-2218132000000),(-13084000000),(-623586975028)⟩
theorem rev191_plane66_mem : rev191_plane66 ∈ rev191_planes := by decide
def rev191_plane71 : IntegerPlane := ⟨(-643972000000),2044968000000,1318460524019⟩
theorem rev191_plane71_mem : rev191_plane71 ∈ rev191_planes := by decide
def rev191_vertex0 : FractionPoint := fractionRow191[0]!
theorem rev191_vertex0_mem : rev191_vertex0∈fractionRow191 := by decide
def rev191_vertex1 : FractionPoint := fractionRow191[1]!
theorem rev191_vertex1_mem : rev191_vertex1∈fractionRow191 := by decide
def rev191_vertex2 : FractionPoint := fractionRow191[2]!
theorem rev191_vertex2_mem : rev191_vertex2∈fractionRow191 := by decide
def rev191_vertex3 : FractionPoint := fractionRow191[3]!
theorem rev191_vertex3_mem : rev191_vertex3∈fractionRow191 := by decide
def rev191_vertex4 : FractionPoint := fractionRow191[4]!
theorem rev191_vertex4_mem : rev191_vertex4∈fractionRow191 := by decide
def rev191_s0_ll : FractionPoint := ⟨314491167913198627,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev191_s0_ll_mem : rev191_s0_ll.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane66 rev191_vertex4 rev191_vertex0 rev191_s0_ll
    rev191_vertex4_mem rev191_vertex0_mem (by decide)
def rev191_s0_lr : FractionPoint := ⟨50875247919,183754000000,132878752081,183754000000⟩
theorem rev191_s0_lr_mem : rev191_s0_lr.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane66 rev191_vertex4 rev191_vertex0 rev191_s0_lr
    rev191_vertex4_mem rev191_vertex0_mem (by decide)
def rev191_s0_ul : FractionPoint := ⟨314491167913198627,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev191_s0_ul_mem : rev191_s0_ul.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane71 rev191_vertex4 rev191_vertex3 rev191_s0_ul
    rev191_vertex4_mem rev191_vertex3_mem (by decide)
def rev191_s0_ur : FractionPoint := ⟨50875247919,183754000000,137517315141740797,187885524936000000⟩
theorem rev191_s0_ur_mem : rev191_s0_ur.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane71 rev191_vertex4 rev191_vertex3 rev191_s0_ur
    rev191_vertex4_mem rev191_vertex3_mem (by decide)
theorem rev191_slab0 (p : Point) (hp : p∈IntegerCarrier rev191_planes)
    (hx0 : rev191_s0_ll.real.1≤p.1) (hx1 : p.1≤rev191_s0_lr.real.1) :
    p∈rationalHull (fractionRow191.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev191_plane66 rev191_plane71 rev191_s0_ll rev191_s0_lr rev191_s0_ul rev191_s0_ur
    (by decide) rev191_s0_ll_mem rev191_s0_lr_mem rev191_s0_ul_mem rev191_s0_ur_mem p
    (hp _ rev191_plane66_mem) (hp _ rev191_plane71_mem) hx0 hx1
def rev191_s1_ll : FractionPoint := ⟨50875247919,183754000000,132878752081,183754000000⟩
theorem rev191_s1_ll_mem : rev191_s1_ll.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane13 rev191_vertex0 rev191_vertex1 rev191_s1_ll
    rev191_vertex0_mem rev191_vertex1_mem (by decide)
def rev191_s1_lr : FractionPoint := ⟨1862939987124017,5093487332000000,2041015841614715754069,2824506810675956000000⟩
theorem rev191_s1_lr_mem : rev191_s1_lr.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane13 rev191_vertex0 rev191_vertex1 rev191_s1_lr
    rev191_vertex0_mem rev191_vertex1_mem (by decide)
def rev191_s1_ul : FractionPoint := ⟨50875247919,183754000000,137517315141740797,187885524936000000⟩
theorem rev191_s1_ul_mem : rev191_s1_ul.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane71 rev191_vertex4 rev191_vertex3 rev191_s1_ul
    rev191_vertex4_mem rev191_vertex3_mem (by decide)
def rev191_s1_ur : FractionPoint := ⟨1862939987124017,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev191_s1_ur_mem : rev191_s1_ur.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane71 rev191_vertex4 rev191_vertex3 rev191_s1_ur
    rev191_vertex4_mem rev191_vertex3_mem (by decide)
theorem rev191_slab1 (p : Point) (hp : p∈IntegerCarrier rev191_planes)
    (hx0 : rev191_s1_ll.real.1≤p.1) (hx1 : p.1≤rev191_s1_lr.real.1) :
    p∈rationalHull (fractionRow191.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev191_plane13 rev191_plane71 rev191_s1_ll rev191_s1_lr rev191_s1_ul rev191_s1_ur
    (by decide) rev191_s1_ll_mem rev191_s1_lr_mem rev191_s1_ul_mem rev191_s1_ur_mem p
    (hp _ rev191_plane13_mem) (hp _ rev191_plane71_mem) hx0 hx1
def rev191_s2_ll : FractionPoint := ⟨1862939987124017,5093487332000000,2041015841614715754069,2824506810675956000000⟩
theorem rev191_s2_ll_mem : rev191_s2_ll.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane13 rev191_vertex0 rev191_vertex1 rev191_s2_ll
    rev191_vertex0_mem rev191_vertex1_mem (by decide)
def rev191_s2_lr : FractionPoint := ⟨3270661284241,7332499000000,1468143110716894473,2033056333983500000⟩
theorem rev191_s2_lr_mem : rev191_s2_lr.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane13 rev191_vertex0 rev191_vertex1 rev191_s2_lr
    rev191_vertex0_mem rev191_vertex1_mem (by decide)
def rev191_s2_ul : FractionPoint := ⟨1862939987124017,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev191_s2_ul_mem : rev191_s2_ul.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane48 rev191_vertex3 rev191_vertex2 rev191_s2_ul
    rev191_vertex3_mem rev191_vertex2_mem (by decide)
def rev191_s2_ur : FractionPoint := ⟨3270661284241,7332499000000,80699534251423,109987485000000⟩
theorem rev191_s2_ur_mem : rev191_s2_ur.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane48 rev191_vertex3 rev191_vertex2 rev191_s2_ur
    rev191_vertex3_mem rev191_vertex2_mem (by decide)
theorem rev191_slab2 (p : Point) (hp : p∈IntegerCarrier rev191_planes)
    (hx0 : rev191_s2_ll.real.1≤p.1) (hx1 : p.1≤rev191_s2_lr.real.1) :
    p∈rationalHull (fractionRow191.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev191_plane13 rev191_plane48 rev191_s2_ll rev191_s2_lr rev191_s2_ul rev191_s2_ur
    (by decide) rev191_s2_ll_mem rev191_s2_lr_mem rev191_s2_ul_mem rev191_s2_ur_mem p
    (hp _ rev191_plane13_mem) (hp _ rev191_plane48_mem) hx0 hx1
def rev191_s3_ll : FractionPoint := ⟨3270661284241,7332499000000,1468143110716894473,2033056333983500000⟩
theorem rev191_s3_ll_mem : rev191_s3_ll.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane13 rev191_vertex0 rev191_vertex1 rev191_s3_ll
    rev191_vertex0_mem rev191_vertex1_mem (by decide)
def rev191_s3_lr : FractionPoint := ⟨7060476758071777,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev191_s3_lr_mem : rev191_s3_lr.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane13 rev191_vertex0 rev191_vertex1 rev191_s3_lr
    rev191_vertex0_mem rev191_vertex1_mem (by decide)
def rev191_s3_ul : FractionPoint := ⟨3270661284241,7332499000000,80699534251423,109987485000000⟩
theorem rev191_s3_ul_mem : rev191_s3_ul.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane53 rev191_vertex2 rev191_vertex1 rev191_s3_ul
    rev191_vertex2_mem rev191_vertex1_mem (by decide)
def rev191_s3_ur : FractionPoint := ⟨7060476758071777,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev191_s3_ur_mem : rev191_s3_ur.real ∈ rationalHull (fractionRow191.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow191 rev191_plane53 rev191_vertex2 rev191_vertex1 rev191_s3_ur
    rev191_vertex2_mem rev191_vertex1_mem (by decide)
theorem rev191_slab3 (p : Point) (hp : p∈IntegerCarrier rev191_planes)
    (hx0 : rev191_s3_ll.real.1≤p.1) (hx1 : p.1≤rev191_s3_lr.real.1) :
    p∈rationalHull (fractionRow191.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev191_plane13 rev191_plane53 rev191_s3_ll rev191_s3_lr rev191_s3_ul rev191_s3_ur
    (by decide) rev191_s3_ll_mem rev191_s3_lr_mem rev191_s3_ul_mem rev191_s3_ur_mem p
    (hp _ rev191_plane13_mem) (hp _ rev191_plane53_mem) hx0 hx1
theorem rev191_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev191_planes) : rev191_s0_ll.real.1≤p.1 := by
  have hc := rev191_plane66.combine_sound rev191_plane71 2044968000000 13084000000 (by decide) (by decide) p
    (hp _ rev191_plane66_mem) (hp _ rev191_plane71_mem)
  exact (rev191_plane66.combine rev191_plane71 2044968000000 13084000000).xBoundCheck_sound rev191_s0_ll.nx rev191_s0_ll.dx true (by decide) p hc
theorem rev191_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev191_planes) : p.1≤rev191_s3_lr.real.1 := by
  have hc := rev191_plane13.combine_sound rev191_plane53 51300000000 2218132000000 (by decide) (by decide) p
    (hp _ rev191_plane13_mem) (hp _ rev191_plane53_mem)
  exact (rev191_plane13.combine rev191_plane53 51300000000 2218132000000).xBoundCheck_sound rev191_s3_lr.nx rev191_s3_lr.dx false (by decide) p hc
theorem rev191_hull (p : Point) (hp : p∈IntegerCarrier rev191_planes) :
    p∈rationalHull (fractionRow191.map FractionPoint.rational) := by
  have hxlo := rev191_bound0_lo p hp
  have hxhi := rev191_bound0_hi p hp
  by_cases h0 : p.1≤rev191_s0_lr.real.1
  · exact rev191_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev191_s1_lr.real.1
  · exact rev191_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev191_s2_lr.real.1
  · exact rev191_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev191_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull191 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,10,5,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow191 := by
  rw [← fractionRow191_correct]
  exact rev191_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull191
