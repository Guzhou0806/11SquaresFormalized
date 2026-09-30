import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks7
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev60_planes : List IntegerPlane := integerOverlayPlanes ![5,2,7,5]
def rev60_plane27 : IntegerPlane := ⟨(-1855520000000),(-287616000000),(-499376240400)⟩
theorem rev60_plane27_mem : rev60_plane27 ∈ rev60_planes := by decide
def rev60_plane31 : IntegerPlane := ⟨(-2058052000000),1574160000000,(-116004500953)⟩
theorem rev60_plane31_mem : rev60_plane31 ∈ rev60_planes := by decide
def rev60_plane46 : IntegerPlane := ⟨(-1574160000000),2058052000000,116004500953⟩
theorem rev60_plane46_mem : rev60_plane46 ∈ rev60_planes := by decide
def rev60_plane50 : IntegerPlane := ⟨643972000000,2044968000000,726507475981⟩
theorem rev60_plane50_mem : rev60_plane50 ∈ rev60_planes := by decide
def rev60_plane64 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-827972119784)⟩
theorem rev60_plane64_mem : rev60_plane64 ∈ rev60_planes := by decide
def rev60_plane68 : IntegerPlane := ⟨699568000000,(-2144520000000),(-259009891352)⟩
theorem rev60_plane68_mem : rev60_plane68 ∈ rev60_planes := by decide
def rev60_vertex0 : FractionPoint := fractionRow60[0]!
theorem rev60_vertex0_mem : rev60_vertex0∈fractionRow60 := by decide
def rev60_vertex1 : FractionPoint := fractionRow60[1]!
theorem rev60_vertex1_mem : rev60_vertex1∈fractionRow60 := by decide
def rev60_vertex2 : FractionPoint := fractionRow60[2]!
theorem rev60_vertex2_mem : rev60_vertex2∈fractionRow60 := by decide
def rev60_vertex3 : FractionPoint := fractionRow60[3]!
theorem rev60_vertex3_mem : rev60_vertex3∈fractionRow60 := by decide
def rev60_vertex4 : FractionPoint := fractionRow60[4]!
theorem rev60_vertex4_mem : rev60_vertex4∈fractionRow60 := by decide
def rev60_vertex5 : FractionPoint := fractionRow60[5]!
theorem rev60_vertex5_mem : rev60_vertex5∈fractionRow60 := by decide
def rev60_s0_ll : FractionPoint := ⟨304859692386221,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev60_s0_ll_mem : rev60_s0_ll.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane27 rev60_vertex3 rev60_vertex4 rev60_s0_ll
    rev60_vertex3_mem rev60_vertex4_mem (by decide)
def rev60_s0_lr : FractionPoint := ⟨613981986234949,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev60_s0_lr_mem : rev60_s0_lr.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane27 rev60_vertex3 rev60_vertex4 rev60_s0_lr
    rev60_vertex3_mem rev60_vertex4_mem (by decide)
def rev60_s0_ul : FractionPoint := ⟨304859692386221,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev60_s0_ul_mem : rev60_s0_ul.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane31 rev60_vertex3 rev60_vertex2 rev60_s0_ul
    rev60_vertex3_mem rev60_vertex2_mem (by decide)
def rev60_s0_ur : FractionPoint := ⟨613981986234949,2631538706000000,13690521720096798179,59178042420528000000⟩
theorem rev60_s0_ur_mem : rev60_s0_ur.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane31 rev60_vertex3 rev60_vertex2 rev60_s0_ur
    rev60_vertex3_mem rev60_vertex2_mem (by decide)
theorem rev60_slab0 (p : Point) (hp : p∈IntegerCarrier rev60_planes)
    (hx0 : rev60_s0_ll.real.1≤p.1) (hx1 : p.1≤rev60_s0_lr.real.1) :
    p∈rationalHull (fractionRow60.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev60_plane27 rev60_plane31 rev60_s0_ll rev60_s0_lr rev60_s0_ul rev60_s0_ur
    (by decide) rev60_s0_ll_mem rev60_s0_lr_mem rev60_s0_ul_mem rev60_s0_ur_mem p
    (hp _ rev60_plane27_mem) (hp _ rev60_plane31_mem) hx0 hx1
def rev60_s1_ll : FractionPoint := ⟨613981986234949,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev60_s1_ll_mem : rev60_s1_ll.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane64 rev60_vertex4 rev60_vertex5 rev60_s1_ll
    rev60_vertex4_mem rev60_vertex5_mem (by decide)
def rev60_s1_lr : FractionPoint := ⟨116004500953,483892000000,3893152451534813,17172649631200000⟩
theorem rev60_s1_lr_mem : rev60_s1_lr.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane64 rev60_vertex4 rev60_vertex5 rev60_s1_lr
    rev60_vertex4_mem rev60_vertex5_mem (by decide)
def rev60_s1_ul : FractionPoint := ⟨613981986234949,2631538706000000,13690521720096798179,59178042420528000000⟩
theorem rev60_s1_ul_mem : rev60_s1_ul.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane31 rev60_vertex3 rev60_vertex2 rev60_s1_ul
    rev60_vertex3_mem rev60_vertex2_mem (by decide)
def rev60_s1_ur : FractionPoint := ⟨116004500953,483892000000,116004500953,483892000000⟩
theorem rev60_s1_ur_mem : rev60_s1_ur.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane31 rev60_vertex3 rev60_vertex2 rev60_s1_ur
    rev60_vertex3_mem rev60_vertex2_mem (by decide)
theorem rev60_slab1 (p : Point) (hp : p∈IntegerCarrier rev60_planes)
    (hx0 : rev60_s1_ll.real.1≤p.1) (hx1 : p.1≤rev60_s1_lr.real.1) :
    p∈rationalHull (fractionRow60.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev60_plane64 rev60_plane31 rev60_s1_ll rev60_s1_lr rev60_s1_ul rev60_s1_ur
    (by decide) rev60_s1_ll_mem rev60_s1_lr_mem rev60_s1_ul_mem rev60_s1_ur_mem p
    (hp _ rev60_plane64_mem) (hp _ rev60_plane31_mem) hx0 hx1
def rev60_s2_ll : FractionPoint := ⟨116004500953,483892000000,3893152451534813,17172649631200000⟩
theorem rev60_s2_ll_mem : rev60_s2_ll.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane64 rev60_vertex4 rev60_vertex5 rev60_s2_ll
    rev60_vertex4_mem rev60_vertex5_mem (by decide)
def rev60_s2_lr : FractionPoint := ⟨79198296098933,296192993000000,431262268381943,2073350951000000⟩
theorem rev60_s2_lr_mem : rev60_s2_lr.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane64 rev60_vertex4 rev60_vertex5 rev60_s2_lr
    rev60_vertex4_mem rev60_vertex5_mem (by decide)
def rev60_s2_ul : FractionPoint := ⟨116004500953,483892000000,116004500953,483892000000⟩
theorem rev60_s2_ul_mem : rev60_s2_ul.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane46 rev60_vertex2 rev60_vertex1 rev60_s2_ul
    rev60_vertex2_mem rev60_vertex1_mem (by decide)
def rev60_s2_ur : FractionPoint := ⟨79198296098933,296192993000000,159030510125836793609,609580581629636000000⟩
theorem rev60_s2_ur_mem : rev60_s2_ur.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane46 rev60_vertex2 rev60_vertex1 rev60_s2_ur
    rev60_vertex2_mem rev60_vertex1_mem (by decide)
theorem rev60_slab2 (p : Point) (hp : p∈IntegerCarrier rev60_planes)
    (hx0 : rev60_s2_ll.real.1≤p.1) (hx1 : p.1≤rev60_s2_lr.real.1) :
    p∈rationalHull (fractionRow60.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev60_plane64 rev60_plane46 rev60_s2_ll rev60_s2_lr rev60_s2_ul rev60_s2_ur
    (by decide) rev60_s2_ll_mem rev60_s2_lr_mem rev60_s2_ul_mem rev60_s2_ur_mem p
    (hp _ rev60_plane64_mem) (hp _ rev60_plane46_mem) hx0 hx1
def rev60_s3_ll : FractionPoint := ⟨79198296098933,296192993000000,431262268381943,2073350951000000⟩
theorem rev60_s3_ll_mem : rev60_s3_ll.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane68 rev60_vertex5 rev60_vertex0 rev60_s3_ll
    rev60_vertex5_mem rev60_vertex0_mem (by decide)
def rev60_s3_lr : FractionPoint := ⟨314491167913198627,1136108672356000000,465825490168200238187,2206891096051530000000⟩
theorem rev60_s3_lr_mem : rev60_s3_lr.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane68 rev60_vertex5 rev60_vertex0 rev60_s3_lr
    rev60_vertex5_mem rev60_vertex0_mem (by decide)
def rev60_s3_ul : FractionPoint := ⟨79198296098933,296192993000000,159030510125836793609,609580581629636000000⟩
theorem rev60_s3_ul_mem : rev60_s3_ul.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane46 rev60_vertex2 rev60_vertex1 rev60_s3_ul
    rev60_vertex2_mem rev60_vertex1_mem (by decide)
def rev60_s3_ur : FractionPoint := ⟨314491167913198627,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev60_s3_ur_mem : rev60_s3_ur.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane46 rev60_vertex2 rev60_vertex1 rev60_s3_ur
    rev60_vertex2_mem rev60_vertex1_mem (by decide)
theorem rev60_slab3 (p : Point) (hp : p∈IntegerCarrier rev60_planes)
    (hx0 : rev60_s3_ll.real.1≤p.1) (hx1 : p.1≤rev60_s3_lr.real.1) :
    p∈rationalHull (fractionRow60.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev60_plane68 rev60_plane46 rev60_s3_ll rev60_s3_lr rev60_s3_ul rev60_s3_ur
    (by decide) rev60_s3_ll_mem rev60_s3_lr_mem rev60_s3_ul_mem rev60_s3_ur_mem p
    (hp _ rev60_plane68_mem) (hp _ rev60_plane46_mem) hx0 hx1
def rev60_s4_ll : FractionPoint := ⟨314491167913198627,1136108672356000000,465825490168200238187,2206891096051530000000⟩
theorem rev60_s4_ll_mem : rev60_s4_ll.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane68 rev60_vertex5 rev60_vertex0 rev60_s4_ll
    rev60_vertex5_mem rev60_vertex0_mem (by decide)
def rev60_s4_lr : FractionPoint := ⟨1862939987124017,5093487332000000,611446104810513,2546743666000000⟩
theorem rev60_s4_lr_mem : rev60_s4_lr.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane68 rev60_vertex5 rev60_vertex0 rev60_s4_lr
    rev60_vertex5_mem rev60_vertex0_mem (by decide)
def rev60_s4_ul : FractionPoint := ⟨314491167913198627,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev60_s4_ul_mem : rev60_s4_ul.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane50 rev60_vertex1 rev60_vertex0 rev60_s4_ul
    rev60_vertex1_mem rev60_vertex0_mem (by decide)
def rev60_s4_ur : FractionPoint := ⟨1862939987124017,5093487332000000,611446104810513,2546743666000000⟩
theorem rev60_s4_ur_mem : rev60_s4_ur.real ∈ rationalHull (fractionRow60.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow60 rev60_plane50 rev60_vertex1 rev60_vertex0 rev60_s4_ur
    rev60_vertex1_mem rev60_vertex0_mem (by decide)
theorem rev60_slab4 (p : Point) (hp : p∈IntegerCarrier rev60_planes)
    (hx0 : rev60_s4_ll.real.1≤p.1) (hx1 : p.1≤rev60_s4_lr.real.1) :
    p∈rationalHull (fractionRow60.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev60_plane68 rev60_plane50 rev60_s4_ll rev60_s4_lr rev60_s4_ul rev60_s4_ur
    (by decide) rev60_s4_ll_mem rev60_s4_lr_mem rev60_s4_ul_mem rev60_s4_ur_mem p
    (hp _ rev60_plane68_mem) (hp _ rev60_plane50_mem) hx0 hx1
theorem rev60_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev60_planes) : rev60_s0_ll.real.1≤p.1 := by
  have hc := rev60_plane27.combine_sound rev60_plane31 1574160000000 287616000000 (by decide) (by decide) p
    (hp _ rev60_plane27_mem) (hp _ rev60_plane31_mem)
  exact (rev60_plane27.combine rev60_plane31 1574160000000 287616000000).xBoundCheck_sound rev60_s0_ll.nx rev60_s0_ll.dx true (by decide) p hc
theorem rev60_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev60_planes) : p.1≤rev60_s4_lr.real.1 := by
  have hc := rev60_plane50.combine_sound rev60_plane68 2144520000000 2044968000000 (by decide) (by decide) p
    (hp _ rev60_plane50_mem) (hp _ rev60_plane68_mem)
  exact (rev60_plane50.combine rev60_plane68 2144520000000 2044968000000).xBoundCheck_sound rev60_s4_lr.nx rev60_s4_lr.dx false (by decide) p hc
theorem rev60_hull (p : Point) (hp : p∈IntegerCarrier rev60_planes) :
    p∈rationalHull (fractionRow60.map FractionPoint.rational) := by
  have hxlo := rev60_bound0_lo p hp
  have hxhi := rev60_bound0_hi p hp
  by_cases h0 : p.1≤rev60_s0_lr.real.1
  · exact rev60_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev60_s1_lr.real.1
  · exact rev60_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev60_s2_lr.real.1
  · exact rev60_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev60_s3_lr.real.1
  · exact rev60_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev60_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull60 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,2,7,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow60 := by
  rw [← fractionRow60_correct]
  exact rev60_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull60
