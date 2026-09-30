import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks8
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev71_planes : List IntegerPlane := integerOverlayPlanes ![5,7,2,5]
def rev71_plane4 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-827972119784)⟩
theorem rev71_plane4_mem : rev71_plane4 ∈ rev71_planes := by decide
def rev71_plane8 : IntegerPlane := ⟨(-2144520000000),699568000000,(-259009891352)⟩
theorem rev71_plane8_mem : rev71_plane8 ∈ rev71_planes := by decide
def rev71_plane26 : IntegerPlane := ⟨2058052000000,(-1574160000000),116004500953⟩
theorem rev71_plane26_mem : rev71_plane26 ∈ rev71_planes := by decide
def rev71_plane30 : IntegerPlane := ⟨2044968000000,643972000000,726507475981⟩
theorem rev71_plane30_mem : rev71_plane30 ∈ rev71_planes := by decide
def rev71_plane47 : IntegerPlane := ⟨(-287616000000),(-1855520000000),(-499376240400)⟩
theorem rev71_plane47_mem : rev71_plane47 ∈ rev71_planes := by decide
def rev71_plane51 : IntegerPlane := ⟨1574160000000,(-2058052000000),(-116004500953)⟩
theorem rev71_plane51_mem : rev71_plane51 ∈ rev71_planes := by decide
def rev71_vertex0 : FractionPoint := fractionRow71[0]!
theorem rev71_vertex0_mem : rev71_vertex0∈fractionRow71 := by decide
def rev71_vertex1 : FractionPoint := fractionRow71[1]!
theorem rev71_vertex1_mem : rev71_vertex1∈fractionRow71 := by decide
def rev71_vertex2 : FractionPoint := fractionRow71[2]!
theorem rev71_vertex2_mem : rev71_vertex2∈fractionRow71 := by decide
def rev71_vertex3 : FractionPoint := fractionRow71[3]!
theorem rev71_vertex3_mem : rev71_vertex3∈fractionRow71 := by decide
def rev71_vertex4 : FractionPoint := fractionRow71[4]!
theorem rev71_vertex4_mem : rev71_vertex4∈fractionRow71 := by decide
def rev71_vertex5 : FractionPoint := fractionRow71[5]!
theorem rev71_vertex5_mem : rev71_vertex5∈fractionRow71 := by decide
def rev71_s0_ll : FractionPoint := ⟨431262268381943,2073350951000000,79198296098933,296192993000000⟩
theorem rev71_s0_ll_mem : rev71_s0_ll.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane4 rev71_vertex1 rev71_vertex2 rev71_s0_ll
    rev71_vertex1_mem rev71_vertex2_mem (by decide)
def rev71_s0_lr : FractionPoint := ⟨2553622230880379,11052462565200000,613981986234949,2631538706000000⟩
theorem rev71_s0_lr_mem : rev71_s0_lr.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane4 rev71_vertex1 rev71_vertex2 rev71_s0_lr
    rev71_vertex1_mem rev71_vertex2_mem (by decide)
def rev71_s0_ul : FractionPoint := ⟨431262268381943,2073350951000000,79198296098933,296192993000000⟩
theorem rev71_s0_ul_mem : rev71_s0_ul.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane8 rev71_vertex1 rev71_vertex0 rev71_s0_ul
    rev71_vertex1_mem rev71_vertex0_mem (by decide)
def rev71_s0_ur : FractionPoint := ⟨2553622230880379,11052462565200000,3381983460640645907,10005110160212000000⟩
theorem rev71_s0_ur_mem : rev71_s0_ur.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane8 rev71_vertex1 rev71_vertex0 rev71_s0_ur
    rev71_vertex1_mem rev71_vertex0_mem (by decide)
theorem rev71_slab0 (p : Point) (hp : p∈IntegerCarrier rev71_planes)
    (hx0 : rev71_s0_ll.real.1≤p.1) (hx1 : p.1≤rev71_s0_lr.real.1) :
    p∈rationalHull (fractionRow71.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev71_plane4 rev71_plane8 rev71_s0_ll rev71_s0_lr rev71_s0_ul rev71_s0_ur
    (by decide) rev71_s0_ll_mem rev71_s0_lr_mem rev71_s0_ul_mem rev71_s0_ur_mem p
    (hp _ rev71_plane4_mem) (hp _ rev71_plane8_mem) hx0 hx1
def rev71_s1_ll : FractionPoint := ⟨2553622230880379,11052462565200000,613981986234949,2631538706000000⟩
theorem rev71_s1_ll_mem : rev71_s1_ll.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane47 rev71_vertex2 rev71_vertex3 rev71_s1_ll
    rev71_vertex2_mem rev71_vertex3_mem (by decide)
def rev71_s1_lr : FractionPoint := ⟨5078084991871189,21955087795200000,304859692386221,1306850464000000⟩
theorem rev71_s1_lr_mem : rev71_s1_lr.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane47 rev71_vertex2 rev71_vertex3 rev71_s1_lr
    rev71_vertex2_mem rev71_vertex3_mem (by decide)
def rev71_s1_ul : FractionPoint := ⟨2553622230880379,11052462565200000,3381983460640645907,10005110160212000000⟩
theorem rev71_s1_ul_mem : rev71_s1_ul.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane8 rev71_vertex1 rev71_vertex0 rev71_s1_ul
    rev71_vertex1_mem rev71_vertex0_mem (by decide)
def rev71_s1_ur : FractionPoint := ⟨5078084991871189,21955087795200000,6733268533008836707,19874581856512000000⟩
theorem rev71_s1_ur_mem : rev71_s1_ur.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane8 rev71_vertex1 rev71_vertex0 rev71_s1_ur
    rev71_vertex1_mem rev71_vertex0_mem (by decide)
theorem rev71_slab1 (p : Point) (hp : p∈IntegerCarrier rev71_planes)
    (hx0 : rev71_s1_ll.real.1≤p.1) (hx1 : p.1≤rev71_s1_lr.real.1) :
    p∈rationalHull (fractionRow71.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev71_plane47 rev71_plane8 rev71_s1_ll rev71_s1_lr rev71_s1_ul rev71_s1_ur
    (by decide) rev71_s1_ll_mem rev71_s1_lr_mem rev71_s1_ul_mem rev71_s1_ur_mem p
    (hp _ rev71_plane47_mem) (hp _ rev71_plane8_mem) hx0 hx1
def rev71_s2_ll : FractionPoint := ⟨5078084991871189,21955087795200000,304859692386221,1306850464000000⟩
theorem rev71_s2_ll_mem : rev71_s2_ll.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane51 rev71_vertex3 rev71_vertex4 rev71_s2_ll
    rev71_vertex3_mem rev71_vertex4_mem (by decide)
def rev71_s2_lr : FractionPoint := ⟨116004500953,483892000000,116004500953,483892000000⟩
theorem rev71_s2_lr_mem : rev71_s2_lr.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane51 rev71_vertex3 rev71_vertex4 rev71_s2_lr
    rev71_vertex3_mem rev71_vertex4_mem (by decide)
def rev71_s2_ul : FractionPoint := ⟨5078084991871189,21955087795200000,6733268533008836707,19874581856512000000⟩
theorem rev71_s2_ul_mem : rev71_s2_ul.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane8 rev71_vertex1 rev71_vertex0 rev71_s2_ul
    rev71_vertex1_mem rev71_vertex0_mem (by decide)
def rev71_s2_ur : FractionPoint := ⟨116004500953,483892000000,670875858900139,1839757384000000⟩
theorem rev71_s2_ur_mem : rev71_s2_ur.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane8 rev71_vertex1 rev71_vertex0 rev71_s2_ur
    rev71_vertex1_mem rev71_vertex0_mem (by decide)
theorem rev71_slab2 (p : Point) (hp : p∈IntegerCarrier rev71_planes)
    (hx0 : rev71_s2_ll.real.1≤p.1) (hx1 : p.1≤rev71_s2_lr.real.1) :
    p∈rationalHull (fractionRow71.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev71_plane51 rev71_plane8 rev71_s2_ll rev71_s2_lr rev71_s2_ul rev71_s2_ur
    (by decide) rev71_s2_ll_mem rev71_s2_lr_mem rev71_s2_ul_mem rev71_s2_ur_mem p
    (hp _ rev71_plane51_mem) (hp _ rev71_plane8_mem) hx0 hx1
def rev71_s3_ll : FractionPoint := ⟨116004500953,483892000000,116004500953,483892000000⟩
theorem rev71_s3_ll_mem : rev71_s3_ll.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane26 rev71_vertex4 rev71_vertex5 rev71_s3_ll
    rev71_vertex4_mem rev71_vertex5_mem (by decide)
def rev71_s3_lr : FractionPoint := ⟨611446104810513,2546743666000000,481477075433971093489,2004491004635280000000⟩
theorem rev71_s3_lr_mem : rev71_s3_lr.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane26 rev71_vertex4 rev71_vertex5 rev71_s3_lr
    rev71_vertex4_mem rev71_vertex5_mem (by decide)
def rev71_s3_ul : FractionPoint := ⟨116004500953,483892000000,670875858900139,1839757384000000⟩
theorem rev71_s3_ul_mem : rev71_s3_ul.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane8 rev71_vertex1 rev71_vertex0 rev71_s3_ul
    rev71_vertex1_mem rev71_vertex0_mem (by decide)
def rev71_s3_ur : FractionPoint := ⟨611446104810513,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev71_s3_ur_mem : rev71_s3_ur.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane8 rev71_vertex1 rev71_vertex0 rev71_s3_ur
    rev71_vertex1_mem rev71_vertex0_mem (by decide)
theorem rev71_slab3 (p : Point) (hp : p∈IntegerCarrier rev71_planes)
    (hx0 : rev71_s3_ll.real.1≤p.1) (hx1 : p.1≤rev71_s3_lr.real.1) :
    p∈rationalHull (fractionRow71.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev71_plane26 rev71_plane8 rev71_s3_ll rev71_s3_lr rev71_s3_ul rev71_s3_ur
    (by decide) rev71_s3_ll_mem rev71_s3_lr_mem rev71_s3_ul_mem rev71_s3_ur_mem p
    (hp _ rev71_plane26_mem) (hp _ rev71_plane8_mem) hx0 hx1
def rev71_s4_ll : FractionPoint := ⟨611446104810513,2546743666000000,481477075433971093489,2004491004635280000000⟩
theorem rev71_s4_ll_mem : rev71_s4_ll.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane26 rev71_vertex4 rev71_vertex5 rev71_s4_ll
    rev71_vertex4_mem rev71_vertex5_mem (by decide)
def rev71_s4_lr : FractionPoint := ⟨43512237817069867,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev71_s4_lr_mem : rev71_s4_lr.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane26 rev71_vertex4 rev71_vertex5 rev71_s4_lr
    rev71_vertex4_mem rev71_vertex5_mem (by decide)
def rev71_s4_ul : FractionPoint := ⟨611446104810513,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev71_s4_ul_mem : rev71_s4_ul.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane30 rev71_vertex0 rev71_vertex5 rev71_s4_ul
    rev71_vertex0_mem rev71_vertex5_mem (by decide)
def rev71_s4_ur : FractionPoint := ⟨43512237817069867,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev71_s4_ur_mem : rev71_s4_ur.real ∈ rationalHull (fractionRow71.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow71 rev71_plane30 rev71_vertex0 rev71_vertex5 rev71_s4_ur
    rev71_vertex0_mem rev71_vertex5_mem (by decide)
theorem rev71_slab4 (p : Point) (hp : p∈IntegerCarrier rev71_planes)
    (hx0 : rev71_s4_ll.real.1≤p.1) (hx1 : p.1≤rev71_s4_lr.real.1) :
    p∈rationalHull (fractionRow71.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev71_plane26 rev71_plane30 rev71_s4_ll rev71_s4_lr rev71_s4_ul rev71_s4_ur
    (by decide) rev71_s4_ll_mem rev71_s4_lr_mem rev71_s4_ul_mem rev71_s4_ur_mem p
    (hp _ rev71_plane26_mem) (hp _ rev71_plane30_mem) hx0 hx1
theorem rev71_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev71_planes) : rev71_s0_ll.real.1≤p.1 := by
  have hc := rev71_plane4.combine_sound rev71_plane8 699568000000 1440116000000 (by decide) (by decide) p
    (hp _ rev71_plane4_mem) (hp _ rev71_plane8_mem)
  exact (rev71_plane4.combine rev71_plane8 699568000000 1440116000000).xBoundCheck_sound rev71_s0_ll.nx rev71_s0_ll.dx true (by decide) p hc
theorem rev71_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev71_planes) : p.1≤rev71_s4_lr.real.1 := by
  have hc := rev71_plane26.combine_sound rev71_plane30 643972000000 1574160000000 (by decide) (by decide) p
    (hp _ rev71_plane26_mem) (hp _ rev71_plane30_mem)
  exact (rev71_plane26.combine rev71_plane30 643972000000 1574160000000).xBoundCheck_sound rev71_s4_lr.nx rev71_s4_lr.dx false (by decide) p hc
theorem rev71_hull (p : Point) (hp : p∈IntegerCarrier rev71_planes) :
    p∈rationalHull (fractionRow71.map FractionPoint.rational) := by
  have hxlo := rev71_bound0_lo p hp
  have hxhi := rev71_bound0_hi p hp
  by_cases h0 : p.1≤rev71_s0_lr.real.1
  · exact rev71_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev71_s1_lr.real.1
  · exact rev71_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev71_s2_lr.real.1
  · exact rev71_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev71_s3_lr.real.1
  · exact rev71_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev71_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull71 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,7,2,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow71 := by
  rw [← fractionRow71_correct]
  exact rev71_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull71
