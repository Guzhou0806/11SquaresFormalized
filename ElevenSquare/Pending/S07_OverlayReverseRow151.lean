import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks18
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev151_planes : List IntegerPlane := integerOverlayPlanes ![10,9,13,10]
def rev151_plane10 : IntegerPlane := ⟨51300000000,(-2168356000000),(-1163521164456)⟩
theorem rev151_plane10_mem : rev151_plane10 ∈ rev151_planes := by decide
def rev151_plane15 : IntegerPlane := ⟨2144520000000,(-699568000000),1185942108648⟩
theorem rev151_plane15_mem : rev151_plane15 ∈ rev151_planes := by decide
def rev151_plane32 : IntegerPlane := ⟨2044968000000,643972000000,1962432524019⟩
theorem rev151_plane32_mem : rev151_plane32 ∈ rev151_planes := by decide
def rev151_plane37 : IntegerPlane := ⟨(-13084000000),2218132000000,1594545024972⟩
theorem rev151_plane37_mem : rev151_plane37 ∈ rev151_planes := by decide
def rev151_plane53 : IntegerPlane := ⟨(-2218132000000),13084000000,(-1594545024972)⟩
theorem rev151_plane53_mem : rev151_plane53 ∈ rev151_planes := by decide
def rev151_vertex0 : FractionPoint := fractionRow151[0]!
theorem rev151_vertex0_mem : rev151_vertex0∈fractionRow151 := by decide
def rev151_vertex1 : FractionPoint := fractionRow151[1]!
theorem rev151_vertex1_mem : rev151_vertex1∈fractionRow151 := by decide
def rev151_vertex2 : FractionPoint := fractionRow151[2]!
theorem rev151_vertex2_mem : rev151_vertex2∈fractionRow151 := by decide
def rev151_vertex3 : FractionPoint := fractionRow151[3]!
theorem rev151_vertex3_mem : rev151_vertex3∈fractionRow151 := by decide
def rev151_vertex4 : FractionPoint := fractionRow151[4]!
theorem rev151_vertex4_mem : rev151_vertex4∈fractionRow151 := by decide
def rev151_s0_ll : FractionPoint := ⟨11423568365407659,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev151_s0_ll_mem : rev151_s0_ll.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane10 rev151_vertex0 rev151_vertex1 rev151_s0_ll
    rev151_vertex0_mem rev151_vertex1_mem (by decide)
def rev151_s0_lr : FractionPoint := ⟨132878752081,183754000000,2902873000463199,5242685374000000⟩
theorem rev151_s0_lr_mem : rev151_s0_lr.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane10 rev151_vertex0 rev151_vertex1 rev151_s0_lr
    rev151_vertex0_mem rev151_vertex1_mem (by decide)
def rev151_s0_ul : FractionPoint := ⟨11423568365407659,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev151_s0_ul_mem : rev151_s0_ul.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane53 rev151_vertex0 rev151_vertex4 rev151_s0_ul
    rev151_vertex0_mem rev151_vertex4_mem (by decide)
def rev151_s0_ur : FractionPoint := ⟨132878752081,183754000000,132878752081,183754000000⟩
theorem rev151_s0_ur_mem : rev151_s0_ur.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane53 rev151_vertex0 rev151_vertex4 rev151_s0_ur
    rev151_vertex0_mem rev151_vertex4_mem (by decide)
theorem rev151_slab0 (p : Point) (hp : p∈IntegerCarrier rev151_planes)
    (hx0 : rev151_s0_ll.real.1≤p.1) (hx1 : p.1≤rev151_s0_lr.real.1) :
    p∈rationalHull (fractionRow151.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev151_plane10 rev151_plane53 rev151_s0_ll rev151_s0_lr rev151_s0_ul rev151_s0_ur
    (by decide) rev151_s0_ll_mem rev151_s0_lr_mem rev151_s0_ul_mem rev151_s0_ur_mem p
    (hp _ rev151_plane10_mem) (hp _ rev151_plane53_mem) hx0 hx1
def rev151_s1_ll : FractionPoint := ⟨132878752081,183754000000,2902873000463199,5242685374000000⟩
theorem rev151_s1_ll_mem : rev151_s1_ll.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane10 rev151_vertex0 rev151_vertex1 rev151_s1_ll
    rev151_vertex0_mem rev151_vertex1_mem (by decide)
def rev151_s1_lr : FractionPoint := ⟨118789001090930133,162301238908000000,2564931608458583285223,4630616647284148000000⟩
theorem rev151_s1_lr_mem : rev151_s1_lr.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane10 rev151_vertex0 rev151_vertex1 rev151_s1_lr
    rev151_vertex0_mem rev151_vertex1_mem (by decide)
def rev151_s1_ul : FractionPoint := ⟨132878752081,183754000000,132878752081,183754000000⟩
theorem rev151_s1_ul_mem : rev151_s1_ul.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane37 rev151_vertex4 rev151_vertex3 rev151_s1_ul
    rev151_vertex4_mem rev151_vertex3_mem (by decide)
def rev151_s1_ur : FractionPoint := ⟨118789001090930133,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev151_s1_ur_mem : rev151_s1_ur.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane37 rev151_vertex4 rev151_vertex3 rev151_s1_ur
    rev151_vertex4_mem rev151_vertex3_mem (by decide)
theorem rev151_slab1 (p : Point) (hp : p∈IntegerCarrier rev151_planes)
    (hx0 : rev151_s1_ll.real.1≤p.1) (hx1 : p.1≤rev151_s1_lr.real.1) :
    p∈rationalHull (fractionRow151.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev151_plane10 rev151_plane37 rev151_s1_ll rev151_s1_lr rev151_s1_ul rev151_s1_ur
    (by decide) rev151_s1_ll_mem rev151_s1_lr_mem rev151_s1_ul_mem rev151_s1_ur_mem p
    (hp _ rev151_plane10_mem) (hp _ rev151_plane37_mem) hx0 hx1
def rev151_s2_ll : FractionPoint := ⟨118789001090930133,162301238908000000,2564931608458583285223,4630616647284148000000⟩
theorem rev151_s2_ll_mem : rev151_s2_ll.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane10 rev151_vertex0 rev151_vertex1 rev151_s2_ll
    rev151_vertex0_mem rev151_vertex1_mem (by decide)
def rev151_s2_lr : FractionPoint := ⟨80699534251423,109987485000000,4061837715759,7332499000000⟩
theorem rev151_s2_lr_mem : rev151_s2_lr.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane10 rev151_vertex0 rev151_vertex1 rev151_s2_lr
    rev151_vertex0_mem rev151_vertex1_mem (by decide)
def rev151_s2_ul : FractionPoint := ⟨118789001090930133,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev151_s2_ul_mem : rev151_s2_ul.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane32 rev151_vertex3 rev151_vertex2 rev151_s2_ul
    rev151_vertex3_mem rev151_vertex2_mem (by decide)
def rev151_s2_ur : FractionPoint := ⟨80699534251423,109987485000000,16938350879995970917,23609620230140000000⟩
theorem rev151_s2_ur_mem : rev151_s2_ur.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane32 rev151_vertex3 rev151_vertex2 rev151_s2_ur
    rev151_vertex3_mem rev151_vertex2_mem (by decide)
theorem rev151_slab2 (p : Point) (hp : p∈IntegerCarrier rev151_planes)
    (hx0 : rev151_s2_ll.real.1≤p.1) (hx1 : p.1≤rev151_s2_lr.real.1) :
    p∈rationalHull (fractionRow151.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev151_plane10 rev151_plane32 rev151_s2_ll rev151_s2_lr rev151_s2_ul rev151_s2_ur
    (by decide) rev151_s2_ll_mem rev151_s2_lr_mem rev151_s2_ul_mem rev151_s2_ur_mem p
    (hp _ rev151_plane10_mem) (hp _ rev151_plane32_mem) hx0 hx1
def rev151_s3_ll : FractionPoint := ⟨80699534251423,109987485000000,4061837715759,7332499000000⟩
theorem rev151_s3_ll_mem : rev151_s3_ll.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane15 rev151_vertex1 rev151_vertex2 rev151_s3_ll
    rev151_vertex1_mem rev151_vertex2_mem (by decide)
def rev151_s3_lr : FractionPoint := ⟨1935297561189487,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev151_s3_lr_mem : rev151_s3_lr.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane15 rev151_vertex1 rev151_vertex2 rev151_s3_lr
    rev151_vertex1_mem rev151_vertex2_mem (by decide)
def rev151_s3_ul : FractionPoint := ⟨80699534251423,109987485000000,16938350879995970917,23609620230140000000⟩
theorem rev151_s3_ul_mem : rev151_s3_ul.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane32 rev151_vertex3 rev151_vertex2 rev151_s3_ul
    rev151_vertex3_mem rev151_vertex2_mem (by decide)
def rev151_s3_ur : FractionPoint := ⟨1935297561189487,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev151_s3_ur_mem : rev151_s3_ur.real ∈ rationalHull (fractionRow151.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow151 rev151_plane32 rev151_vertex3 rev151_vertex2 rev151_s3_ur
    rev151_vertex3_mem rev151_vertex2_mem (by decide)
theorem rev151_slab3 (p : Point) (hp : p∈IntegerCarrier rev151_planes)
    (hx0 : rev151_s3_ll.real.1≤p.1) (hx1 : p.1≤rev151_s3_lr.real.1) :
    p∈rationalHull (fractionRow151.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev151_plane15 rev151_plane32 rev151_s3_ll rev151_s3_lr rev151_s3_ul rev151_s3_ur
    (by decide) rev151_s3_ll_mem rev151_s3_lr_mem rev151_s3_ul_mem rev151_s3_ur_mem p
    (hp _ rev151_plane15_mem) (hp _ rev151_plane32_mem) hx0 hx1
theorem rev151_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev151_planes) : rev151_s0_ll.real.1≤p.1 := by
  have hc := rev151_plane10.combine_sound rev151_plane53 13084000000 2168356000000 (by decide) (by decide) p
    (hp _ rev151_plane10_mem) (hp _ rev151_plane53_mem)
  exact (rev151_plane10.combine rev151_plane53 13084000000 2168356000000).xBoundCheck_sound rev151_s0_ll.nx rev151_s0_ll.dx true (by decide) p hc
theorem rev151_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev151_planes) : p.1≤rev151_s3_lr.real.1 := by
  have hc := rev151_plane15.combine_sound rev151_plane32 643972000000 699568000000 (by decide) (by decide) p
    (hp _ rev151_plane15_mem) (hp _ rev151_plane32_mem)
  exact (rev151_plane15.combine rev151_plane32 643972000000 699568000000).xBoundCheck_sound rev151_s3_lr.nx rev151_s3_lr.dx false (by decide) p hc
theorem rev151_hull (p : Point) (hp : p∈IntegerCarrier rev151_planes) :
    p∈rationalHull (fractionRow151.map FractionPoint.rational) := by
  have hxlo := rev151_bound0_lo p hp
  have hxhi := rev151_bound0_hi p hp
  by_cases h0 : p.1≤rev151_s0_lr.real.1
  · exact rev151_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev151_s1_lr.real.1
  · exact rev151_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev151_s2_lr.real.1
  · exact rev151_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev151_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull151 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,9,13,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow151 := by
  rw [← fractionRow151_correct]
  exact rev151_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull151
