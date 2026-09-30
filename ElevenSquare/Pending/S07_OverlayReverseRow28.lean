import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks3
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev28_planes : List IntegerPlane := integerOverlayPlanes ![2,5,10,9]
def rev28_plane10 : IntegerPlane := ⟨13084000000,2218132000000,623586975028⟩
theorem rev28_plane10_mem : rev28_plane10 ∈ rev28_planes := by decide
def rev28_plane50 : IntegerPlane := ⟨(-2168356000000),(-51300000000),(-1214821164456)⟩
theorem rev28_plane50_mem : rev28_plane50 ∈ rev28_planes := by decide
def rev28_plane55 : IntegerPlane := ⟨(-699568000000),(-2144520000000),(-958577891352)⟩
theorem rev28_plane55_mem : rev28_plane55 ∈ rev28_planes := by decide
def rev28_plane72 : IntegerPlane := ⟨643972000000,(-2044968000000),(-82535475981)⟩
theorem rev28_plane72_mem : rev28_plane72 ∈ rev28_planes := by decide
def rev28_plane77 : IntegerPlane := ⟨2218132000000,13084000000,1607629024972⟩
theorem rev28_plane77_mem : rev28_plane77 ∈ rev28_planes := by decide
def rev28_vertex0 : FractionPoint := fractionRow28[0]!
theorem rev28_vertex0_mem : rev28_vertex0∈fractionRow28 := by decide
def rev28_vertex1 : FractionPoint := fractionRow28[1]!
theorem rev28_vertex1_mem : rev28_vertex1∈fractionRow28 := by decide
def rev28_vertex2 : FractionPoint := fractionRow28[2]!
theorem rev28_vertex2_mem : rev28_vertex2∈fractionRow28 := by decide
def rev28_vertex3 : FractionPoint := fractionRow28[3]!
theorem rev28_vertex3_mem : rev28_vertex3∈fractionRow28 := by decide
def rev28_vertex4 : FractionPoint := fractionRow28[4]!
theorem rev28_vertex4_mem : rev28_vertex4∈fractionRow28 := by decide
def rev28_s0_ll : FractionPoint := ⟨8758696339928223,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev28_s0_ll_mem : rev28_s0_ll.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane50 rev28_vertex1 rev28_vertex2 rev28_s0_ll
    rev28_vertex1_mem rev28_vertex2_mem (by decide)
def rev28_s0_lr : FractionPoint := ⟨4061837715759,7332499000000,29287950748577,109987485000000⟩
theorem rev28_s0_lr_mem : rev28_s0_lr.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane50 rev28_vertex1 rev28_vertex2 rev28_s0_lr
    rev28_vertex1_mem rev28_vertex2_mem (by decide)
def rev28_s0_ul : FractionPoint := ⟨8758696339928223,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev28_s0_ul_mem : rev28_s0_ul.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane10 rev28_vertex1 rev28_vertex0 rev28_s0_ul
    rev28_vertex1_mem rev28_vertex0_mem (by decide)
def rev28_s0_ur : FractionPoint := ⟨4061837715759,7332499000000,564913223266605527,2033056333983500000⟩
theorem rev28_s0_ur_mem : rev28_s0_ur.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane10 rev28_vertex1 rev28_vertex0 rev28_s0_ur
    rev28_vertex1_mem rev28_vertex0_mem (by decide)
theorem rev28_slab0 (p : Point) (hp : p∈IntegerCarrier rev28_planes)
    (hx0 : rev28_s0_ll.real.1≤p.1) (hx1 : p.1≤rev28_s0_lr.real.1) :
    p∈rationalHull (fractionRow28.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev28_plane50 rev28_plane10 rev28_s0_ll rev28_s0_lr rev28_s0_ul rev28_s0_ur
    (by decide) rev28_s0_ll_mem rev28_s0_lr_mem rev28_s0_ul_mem rev28_s0_ur_mem p
    (hp _ rev28_plane50_mem) (hp _ rev28_plane10_mem) hx0 hx1
def rev28_s1_ll : FractionPoint := ⟨4061837715759,7332499000000,29287950748577,109987485000000⟩
theorem rev28_s1_ll_mem : rev28_s1_ll.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane55 rev28_vertex2 rev28_vertex3 rev28_s1_ll
    rev28_vertex2_mem rev28_vertex3_mem (by decide)
def rev28_s1_lr : FractionPoint := ⟨3230547344875983,5093487332000000,611446104810513,2546743666000000⟩
theorem rev28_s1_lr_mem : rev28_s1_lr.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane55 rev28_vertex2 rev28_vertex3 rev28_s1_lr
    rev28_vertex2_mem rev28_vertex3_mem (by decide)
def rev28_s1_ul : FractionPoint := ⟨4061837715759,7332499000000,564913223266605527,2033056333983500000⟩
theorem rev28_s1_ul_mem : rev28_s1_ul.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane10 rev28_vertex1 rev28_vertex0 rev28_s1_ul
    rev28_vertex1_mem rev28_vertex0_mem (by decide)
def rev28_s1_ur : FractionPoint := ⟨3230547344875983,5093487332000000,783490969061240245931,2824506810675956000000⟩
theorem rev28_s1_ur_mem : rev28_s1_ur.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane10 rev28_vertex1 rev28_vertex0 rev28_s1_ur
    rev28_vertex1_mem rev28_vertex0_mem (by decide)
theorem rev28_slab1 (p : Point) (hp : p∈IntegerCarrier rev28_planes)
    (hx0 : rev28_s1_ll.real.1≤p.1) (hx1 : p.1≤rev28_s1_lr.real.1) :
    p∈rationalHull (fractionRow28.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev28_plane55 rev28_plane10 rev28_s1_ll rev28_s1_lr rev28_s1_ul rev28_s1_ur
    (by decide) rev28_s1_ll_mem rev28_s1_lr_mem rev28_s1_ul_mem rev28_s1_ur_mem p
    (hp _ rev28_plane55_mem) (hp _ rev28_plane10_mem) hx0 hx1
def rev28_s2_ll : FractionPoint := ⟨3230547344875983,5093487332000000,611446104810513,2546743666000000⟩
theorem rev28_s2_ll_mem : rev28_s2_ll.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane72 rev28_vertex3 rev28_vertex4 rev28_s2_ll
    rev28_vertex3_mem rev28_vertex4_mem (by decide)
def rev28_s2_lr : FractionPoint := ⟨132878752081,183754000000,50368209794259203,187885524936000000⟩
theorem rev28_s2_lr_mem : rev28_s2_lr.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane72 rev28_vertex3 rev28_vertex4 rev28_s2_lr
    rev28_vertex3_mem rev28_vertex4_mem (by decide)
def rev28_s2_ul : FractionPoint := ⟨3230547344875983,5093487332000000,783490969061240245931,2824506810675956000000⟩
theorem rev28_s2_ul_mem : rev28_s2_ul.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane10 rev28_vertex1 rev28_vertex0 rev28_s2_ul
    rev28_vertex1_mem rev28_vertex0_mem (by decide)
def rev28_s2_ur : FractionPoint := ⟨132878752081,183754000000,50875247919,183754000000⟩
theorem rev28_s2_ur_mem : rev28_s2_ur.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane10 rev28_vertex1 rev28_vertex0 rev28_s2_ur
    rev28_vertex1_mem rev28_vertex0_mem (by decide)
theorem rev28_slab2 (p : Point) (hp : p∈IntegerCarrier rev28_planes)
    (hx0 : rev28_s2_ll.real.1≤p.1) (hx1 : p.1≤rev28_s2_lr.real.1) :
    p∈rationalHull (fractionRow28.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev28_plane72 rev28_plane10 rev28_s2_ll rev28_s2_lr rev28_s2_ul rev28_s2_ur
    (by decide) rev28_s2_ll_mem rev28_s2_lr_mem rev28_s2_ul_mem rev28_s2_ur_mem p
    (hp _ rev28_plane72_mem) (hp _ rev28_plane10_mem) hx0 hx1
def rev28_s3_ll : FractionPoint := ⟨132878752081,183754000000,50368209794259203,187885524936000000⟩
theorem rev28_s3_ll_mem : rev28_s3_ll.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane72 rev28_vertex3 rev28_vertex4 rev28_s3_ll
    rev28_vertex3_mem rev28_vertex4_mem (by decide)
def rev28_s3_lr : FractionPoint := ⟨821617504442801373,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev28_s3_lr_mem : rev28_s3_lr.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane72 rev28_vertex3 rev28_vertex4 rev28_s3_lr
    rev28_vertex3_mem rev28_vertex4_mem (by decide)
def rev28_s3_ul : FractionPoint := ⟨132878752081,183754000000,50875247919,183754000000⟩
theorem rev28_s3_ul_mem : rev28_s3_ul.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane77 rev28_vertex0 rev28_vertex4 rev28_s3_ul
    rev28_vertex0_mem rev28_vertex4_mem (by decide)
def rev28_s3_ur : FractionPoint := ⟨821617504442801373,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev28_s3_ur_mem : rev28_s3_ur.real ∈ rationalHull (fractionRow28.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow28 rev28_plane77 rev28_vertex0 rev28_vertex4 rev28_s3_ur
    rev28_vertex0_mem rev28_vertex4_mem (by decide)
theorem rev28_slab3 (p : Point) (hp : p∈IntegerCarrier rev28_planes)
    (hx0 : rev28_s3_ll.real.1≤p.1) (hx1 : p.1≤rev28_s3_lr.real.1) :
    p∈rationalHull (fractionRow28.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev28_plane72 rev28_plane77 rev28_s3_ll rev28_s3_lr rev28_s3_ul rev28_s3_ur
    (by decide) rev28_s3_ll_mem rev28_s3_lr_mem rev28_s3_ul_mem rev28_s3_ur_mem p
    (hp _ rev28_plane72_mem) (hp _ rev28_plane77_mem) hx0 hx1
theorem rev28_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev28_planes) : rev28_s0_ll.real.1≤p.1 := by
  have hc := rev28_plane10.combine_sound rev28_plane50 51300000000 2218132000000 (by decide) (by decide) p
    (hp _ rev28_plane10_mem) (hp _ rev28_plane50_mem)
  exact (rev28_plane10.combine rev28_plane50 51300000000 2218132000000).xBoundCheck_sound rev28_s0_ll.nx rev28_s0_ll.dx true (by decide) p hc
theorem rev28_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev28_planes) : p.1≤rev28_s3_lr.real.1 := by
  have hc := rev28_plane72.combine_sound rev28_plane77 13084000000 2044968000000 (by decide) (by decide) p
    (hp _ rev28_plane72_mem) (hp _ rev28_plane77_mem)
  exact (rev28_plane72.combine rev28_plane77 13084000000 2044968000000).xBoundCheck_sound rev28_s3_lr.nx rev28_s3_lr.dx false (by decide) p hc
theorem rev28_hull (p : Point) (hp : p∈IntegerCarrier rev28_planes) :
    p∈rationalHull (fractionRow28.map FractionPoint.rational) := by
  have hxlo := rev28_bound0_lo p hp
  have hxhi := rev28_bound0_hi p hp
  by_cases h0 : p.1≤rev28_s0_lr.real.1
  · exact rev28_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev28_s1_lr.real.1
  · exact rev28_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev28_s2_lr.real.1
  · exact rev28_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev28_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull28 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,5,10,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow28 := by
  rw [← fractionRow28_correct]
  exact rev28_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull28
