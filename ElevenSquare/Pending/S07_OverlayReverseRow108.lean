import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks13
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev108_planes : List IntegerPlane := integerOverlayPlanes ![7,5,10,13]
def rev108_plane6 : IntegerPlane := ⟨(-2058052000000),(-1574160000000),(-1942047499047)⟩
theorem rev108_plane6_mem : rev108_plane6 ∈ rev108_planes := by decide
def rev108_plane10 : IntegerPlane := ⟨(-2044968000000),643972000000,(-1318460524019)⟩
theorem rev108_plane10_mem : rev108_plane10 ∈ rev108_planes := by decide
def rev108_plane24 : IntegerPlane := ⟨2129316000000,(-1440116000000),1301343880216⟩
theorem rev108_plane24_mem : rev108_plane24 ∈ rev108_planes := by decide
def rev108_plane28 : IntegerPlane := ⟨2144520000000,699568000000,1885510108648⟩
theorem rev108_plane28_mem : rev108_plane28 ∈ rev108_planes := by decide
def rev108_plane72 : IntegerPlane := ⟨(-1574160000000),(-2058052000000),(-1690164500953)⟩
theorem rev108_plane72_mem : rev108_plane72 ∈ rev108_planes := by decide
def rev108_plane76 : IntegerPlane := ⟨287616000000,(-1855520000000),(-211760240400)⟩
theorem rev108_plane76_mem : rev108_plane76 ∈ rev108_planes := by decide
def rev108_vertex0 : FractionPoint := fractionRow108[0]!
theorem rev108_vertex0_mem : rev108_vertex0∈fractionRow108 := by decide
def rev108_vertex1 : FractionPoint := fractionRow108[1]!
theorem rev108_vertex1_mem : rev108_vertex1∈fractionRow108 := by decide
def rev108_vertex2 : FractionPoint := fractionRow108[2]!
theorem rev108_vertex2_mem : rev108_vertex2∈fractionRow108 := by decide
def rev108_vertex3 : FractionPoint := fractionRow108[3]!
theorem rev108_vertex3_mem : rev108_vertex3∈fractionRow108 := by decide
def rev108_vertex4 : FractionPoint := fractionRow108[4]!
theorem rev108_vertex4_mem : rev108_vertex4∈fractionRow108 := by decide
def rev108_vertex5 : FractionPoint := fractionRow108[5]!
theorem rev108_vertex5_mem : rev108_vertex5∈fractionRow108 := by decide
def rev108_s0_ll : FractionPoint := ⟨118789001090930133,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev108_s0_ll_mem : rev108_s0_ll.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane6 rev108_vertex1 rev108_vertex2 rev108_s0_ll
    rev108_vertex1_mem rev108_vertex2_mem (by decide)
def rev108_s0_lr : FractionPoint := ⟨1935297561189487,2546743666000000,481477075433971093489,2004491004635280000000⟩
theorem rev108_s0_lr_mem : rev108_s0_lr.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane6 rev108_vertex1 rev108_vertex2 rev108_s0_lr
    rev108_vertex1_mem rev108_vertex2_mem (by decide)
def rev108_s0_ul : FractionPoint := ⟨118789001090930133,162301238908000000,314491167913198627,1136108672356000000⟩
theorem rev108_s0_ul_mem : rev108_s0_ul.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane10 rev108_vertex1 rev108_vertex0 rev108_s0_ul
    rev108_vertex1_mem rev108_vertex0_mem (by decide)
def rev108_s0_ur : FractionPoint := ⟨1935297561189487,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev108_s0_ur_mem : rev108_s0_ur.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane10 rev108_vertex1 rev108_vertex0 rev108_s0_ur
    rev108_vertex1_mem rev108_vertex0_mem (by decide)
theorem rev108_slab0 (p : Point) (hp : p∈IntegerCarrier rev108_planes)
    (hx0 : rev108_s0_ll.real.1≤p.1) (hx1 : p.1≤rev108_s0_lr.real.1) :
    p∈rationalHull (fractionRow108.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev108_plane6 rev108_plane10 rev108_s0_ll rev108_s0_lr rev108_s0_ul rev108_s0_ur
    (by decide) rev108_s0_ll_mem rev108_s0_lr_mem rev108_s0_ul_mem rev108_s0_ur_mem p
    (hp _ rev108_plane6_mem) (hp _ rev108_plane10_mem) hx0 hx1
def rev108_s1_ll : FractionPoint := ⟨1935297561189487,2546743666000000,481477075433971093489,2004491004635280000000⟩
theorem rev108_s1_ll_mem : rev108_s1_ll.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane6 rev108_vertex1 rev108_vertex2 rev108_s1_ll
    rev108_vertex1_mem rev108_vertex2_mem (by decide)
def rev108_s1_lr : FractionPoint := ⟨367887499047,483892000000,116004500953,483892000000⟩
theorem rev108_s1_lr_mem : rev108_s1_lr.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane6 rev108_vertex1 rev108_vertex2 rev108_s1_lr
    rev108_vertex1_mem rev108_vertex2_mem (by decide)
def rev108_s1_ul : FractionPoint := ⟨1935297561189487,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev108_s1_ul_mem : rev108_s1_ul.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane28 rev108_vertex0 rev108_vertex5 rev108_s1_ul
    rev108_vertex0_mem rev108_vertex5_mem (by decide)
def rev108_s1_ur : FractionPoint := ⟨367887499047,483892000000,670875858900139,1839757384000000⟩
theorem rev108_s1_ur_mem : rev108_s1_ur.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane28 rev108_vertex0 rev108_vertex5 rev108_s1_ur
    rev108_vertex0_mem rev108_vertex5_mem (by decide)
theorem rev108_slab1 (p : Point) (hp : p∈IntegerCarrier rev108_planes)
    (hx0 : rev108_s1_ll.real.1≤p.1) (hx1 : p.1≤rev108_s1_lr.real.1) :
    p∈rationalHull (fractionRow108.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev108_plane6 rev108_plane28 rev108_s1_ll rev108_s1_lr rev108_s1_ul rev108_s1_ur
    (by decide) rev108_s1_ll_mem rev108_s1_lr_mem rev108_s1_ul_mem rev108_s1_ur_mem p
    (hp _ rev108_plane6_mem) (hp _ rev108_plane28_mem) hx0 hx1
def rev108_s2_ll : FractionPoint := ⟨367887499047,483892000000,116004500953,483892000000⟩
theorem rev108_s2_ll_mem : rev108_s2_ll.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane72 rev108_vertex2 rev108_vertex3 rev108_s2_ll
    rev108_vertex2_mem rev108_vertex3_mem (by decide)
def rev108_s2_lr : FractionPoint := ⟨16877002803328811,21955087795200000,304859692386221,1306850464000000⟩
theorem rev108_s2_lr_mem : rev108_s2_lr.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane72 rev108_vertex2 rev108_vertex3 rev108_s2_lr
    rev108_vertex2_mem rev108_vertex3_mem (by decide)
def rev108_s2_ul : FractionPoint := ⟨367887499047,483892000000,670875858900139,1839757384000000⟩
theorem rev108_s2_ul_mem : rev108_s2_ul.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane28 rev108_vertex0 rev108_vertex5 rev108_s2_ul
    rev108_vertex0_mem rev108_vertex5_mem (by decide)
def rev108_s2_ur : FractionPoint := ⟨16877002803328811,21955087795200000,6733268533008836707,19874581856512000000⟩
theorem rev108_s2_ur_mem : rev108_s2_ur.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane28 rev108_vertex0 rev108_vertex5 rev108_s2_ur
    rev108_vertex0_mem rev108_vertex5_mem (by decide)
theorem rev108_slab2 (p : Point) (hp : p∈IntegerCarrier rev108_planes)
    (hx0 : rev108_s2_ll.real.1≤p.1) (hx1 : p.1≤rev108_s2_lr.real.1) :
    p∈rationalHull (fractionRow108.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev108_plane72 rev108_plane28 rev108_s2_ll rev108_s2_lr rev108_s2_ul rev108_s2_ur
    (by decide) rev108_s2_ll_mem rev108_s2_lr_mem rev108_s2_ul_mem rev108_s2_ur_mem p
    (hp _ rev108_plane72_mem) (hp _ rev108_plane28_mem) hx0 hx1
def rev108_s3_ll : FractionPoint := ⟨16877002803328811,21955087795200000,304859692386221,1306850464000000⟩
theorem rev108_s3_ll_mem : rev108_s3_ll.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane76 rev108_vertex3 rev108_vertex4 rev108_s3_ll
    rev108_vertex3_mem rev108_vertex4_mem (by decide)
def rev108_s3_lr : FractionPoint := ⟨8498840334319621,11052462565200000,613981986234949,2631538706000000⟩
theorem rev108_s3_lr_mem : rev108_s3_lr.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane76 rev108_vertex3 rev108_vertex4 rev108_s3_lr
    rev108_vertex3_mem rev108_vertex4_mem (by decide)
def rev108_s3_ul : FractionPoint := ⟨16877002803328811,21955087795200000,6733268533008836707,19874581856512000000⟩
theorem rev108_s3_ul_mem : rev108_s3_ul.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane28 rev108_vertex0 rev108_vertex5 rev108_s3_ul
    rev108_vertex0_mem rev108_vertex5_mem (by decide)
def rev108_s3_ur : FractionPoint := ⟨8498840334319621,11052462565200000,3381983460640645907,10005110160212000000⟩
theorem rev108_s3_ur_mem : rev108_s3_ur.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane28 rev108_vertex0 rev108_vertex5 rev108_s3_ur
    rev108_vertex0_mem rev108_vertex5_mem (by decide)
theorem rev108_slab3 (p : Point) (hp : p∈IntegerCarrier rev108_planes)
    (hx0 : rev108_s3_ll.real.1≤p.1) (hx1 : p.1≤rev108_s3_lr.real.1) :
    p∈rationalHull (fractionRow108.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev108_plane76 rev108_plane28 rev108_s3_ll rev108_s3_lr rev108_s3_ul rev108_s3_ur
    (by decide) rev108_s3_ll_mem rev108_s3_lr_mem rev108_s3_ul_mem rev108_s3_ur_mem p
    (hp _ rev108_plane76_mem) (hp _ rev108_plane28_mem) hx0 hx1
def rev108_s4_ll : FractionPoint := ⟨8498840334319621,11052462565200000,613981986234949,2631538706000000⟩
theorem rev108_s4_ll_mem : rev108_s4_ll.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane24 rev108_vertex4 rev108_vertex5 rev108_s4_ll
    rev108_vertex4_mem rev108_vertex5_mem (by decide)
def rev108_s4_lr : FractionPoint := ⟨1642088682618057,2073350951000000,79198296098933,296192993000000⟩
theorem rev108_s4_lr_mem : rev108_s4_lr.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane24 rev108_vertex4 rev108_vertex5 rev108_s4_lr
    rev108_vertex4_mem rev108_vertex5_mem (by decide)
def rev108_s4_ul : FractionPoint := ⟨8498840334319621,11052462565200000,3381983460640645907,10005110160212000000⟩
theorem rev108_s4_ul_mem : rev108_s4_ul.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane28 rev108_vertex0 rev108_vertex5 rev108_s4_ul
    rev108_vertex0_mem rev108_vertex5_mem (by decide)
def rev108_s4_ur : FractionPoint := ⟨1642088682618057,2073350951000000,79198296098933,296192993000000⟩
theorem rev108_s4_ur_mem : rev108_s4_ur.real ∈ rationalHull (fractionRow108.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow108 rev108_plane28 rev108_vertex0 rev108_vertex5 rev108_s4_ur
    rev108_vertex0_mem rev108_vertex5_mem (by decide)
theorem rev108_slab4 (p : Point) (hp : p∈IntegerCarrier rev108_planes)
    (hx0 : rev108_s4_ll.real.1≤p.1) (hx1 : p.1≤rev108_s4_lr.real.1) :
    p∈rationalHull (fractionRow108.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev108_plane24 rev108_plane28 rev108_s4_ll rev108_s4_lr rev108_s4_ul rev108_s4_ur
    (by decide) rev108_s4_ll_mem rev108_s4_lr_mem rev108_s4_ul_mem rev108_s4_ur_mem p
    (hp _ rev108_plane24_mem) (hp _ rev108_plane28_mem) hx0 hx1
theorem rev108_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev108_planes) : rev108_s0_ll.real.1≤p.1 := by
  have hc := rev108_plane6.combine_sound rev108_plane10 643972000000 1574160000000 (by decide) (by decide) p
    (hp _ rev108_plane6_mem) (hp _ rev108_plane10_mem)
  exact (rev108_plane6.combine rev108_plane10 643972000000 1574160000000).xBoundCheck_sound rev108_s0_ll.nx rev108_s0_ll.dx true (by decide) p hc
theorem rev108_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev108_planes) : p.1≤rev108_s4_lr.real.1 := by
  have hc := rev108_plane24.combine_sound rev108_plane28 699568000000 1440116000000 (by decide) (by decide) p
    (hp _ rev108_plane24_mem) (hp _ rev108_plane28_mem)
  exact (rev108_plane24.combine rev108_plane28 699568000000 1440116000000).xBoundCheck_sound rev108_s4_lr.nx rev108_s4_lr.dx false (by decide) p hc
theorem rev108_hull (p : Point) (hp : p∈IntegerCarrier rev108_planes) :
    p∈rationalHull (fractionRow108.map FractionPoint.rational) := by
  have hxlo := rev108_bound0_lo p hp
  have hxhi := rev108_bound0_hi p hp
  by_cases h0 : p.1≤rev108_s0_lr.real.1
  · exact rev108_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev108_s1_lr.real.1
  · exact rev108_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev108_s2_lr.real.1
  · exact rev108_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev108_s3_lr.real.1
  · exact rev108_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev108_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull108 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,5,10,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow108 := by
  rw [← fractionRow108_correct]
  exact rev108_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull108
