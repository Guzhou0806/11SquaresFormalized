import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks24
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev192_planes : List IntegerPlane := integerOverlayPlanes ![13,10,5,7]
def rev192_plane12 : IntegerPlane := ⟨(-2058052000000),(-1574160000000),(-1690164500953)⟩
theorem rev192_plane12_mem : rev192_plane12 ∈ rev192_planes := by decide
def rev192_plane16 : IntegerPlane := ⟨(-1855520000000),287616000000,(-211760240400)⟩
theorem rev192_plane16_mem : rev192_plane16 ∈ rev192_planes := by decide
def rev192_plane44 : IntegerPlane := ⟨(-1440116000000),2129316000000,1301343880216⟩
theorem rev192_plane44_mem : rev192_plane44 ∈ rev192_planes := by decide
def rev192_plane48 : IntegerPlane := ⟨699568000000,2144520000000,1885510108648⟩
theorem rev192_plane48_mem : rev192_plane48 ∈ rev192_planes := by decide
def rev192_plane66 : IntegerPlane := ⟨(-1574160000000),(-2058052000000),(-1942047499047)⟩
theorem rev192_plane66_mem : rev192_plane66 ∈ rev192_planes := by decide
def rev192_plane70 : IntegerPlane := ⟨643972000000,(-2044968000000),(-1318460524019)⟩
theorem rev192_plane70_mem : rev192_plane70 ∈ rev192_planes := by decide
def rev192_vertex0 : FractionPoint := fractionRow192[0]!
theorem rev192_vertex0_mem : rev192_vertex0∈fractionRow192 := by decide
def rev192_vertex1 : FractionPoint := fractionRow192[1]!
theorem rev192_vertex1_mem : rev192_vertex1∈fractionRow192 := by decide
def rev192_vertex2 : FractionPoint := fractionRow192[2]!
theorem rev192_vertex2_mem : rev192_vertex2∈fractionRow192 := by decide
def rev192_vertex3 : FractionPoint := fractionRow192[3]!
theorem rev192_vertex3_mem : rev192_vertex3∈fractionRow192 := by decide
def rev192_vertex4 : FractionPoint := fractionRow192[4]!
theorem rev192_vertex4_mem : rev192_vertex4∈fractionRow192 := by decide
def rev192_vertex5 : FractionPoint := fractionRow192[5]!
theorem rev192_vertex5_mem : rev192_vertex5∈fractionRow192 := by decide
def rev192_s0_ll : FractionPoint := ⟨304859692386221,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev192_s0_ll_mem : rev192_s0_ll.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane12 rev192_vertex1 rev192_vertex2 rev192_s0_ll
    rev192_vertex1_mem rev192_vertex2_mem (by decide)
def rev192_s0_lr : FractionPoint := ⟨613981986234949,2631538706000000,45487520700431201821,59178042420528000000⟩
theorem rev192_s0_lr_mem : rev192_s0_lr.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane12 rev192_vertex1 rev192_vertex2 rev192_s0_lr
    rev192_vertex1_mem rev192_vertex2_mem (by decide)
def rev192_s0_ul : FractionPoint := ⟨304859692386221,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev192_s0_ul_mem : rev192_s0_ul.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane16 rev192_vertex1 rev192_vertex0 rev192_s0_ul
    rev192_vertex1_mem rev192_vertex0_mem (by decide)
def rev192_s0_ur : FractionPoint := ⟨613981986234949,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev192_s0_ur_mem : rev192_s0_ur.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane16 rev192_vertex1 rev192_vertex0 rev192_s0_ur
    rev192_vertex1_mem rev192_vertex0_mem (by decide)
theorem rev192_slab0 (p : Point) (hp : p∈IntegerCarrier rev192_planes)
    (hx0 : rev192_s0_ll.real.1≤p.1) (hx1 : p.1≤rev192_s0_lr.real.1) :
    p∈rationalHull (fractionRow192.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev192_plane12 rev192_plane16 rev192_s0_ll rev192_s0_lr rev192_s0_ul rev192_s0_ur
    (by decide) rev192_s0_ll_mem rev192_s0_lr_mem rev192_s0_ul_mem rev192_s0_ur_mem p
    (hp _ rev192_plane12_mem) (hp _ rev192_plane16_mem) hx0 hx1
def rev192_s1_ll : FractionPoint := ⟨613981986234949,2631538706000000,45487520700431201821,59178042420528000000⟩
theorem rev192_s1_ll_mem : rev192_s1_ll.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane12 rev192_vertex1 rev192_vertex2 rev192_s1_ll
    rev192_vertex1_mem rev192_vertex2_mem (by decide)
def rev192_s1_lr : FractionPoint := ⟨116004500953,483892000000,367887499047,483892000000⟩
theorem rev192_s1_lr_mem : rev192_s1_lr.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane12 rev192_vertex1 rev192_vertex2 rev192_s1_lr
    rev192_vertex1_mem rev192_vertex2_mem (by decide)
def rev192_s1_ul : FractionPoint := ⟨613981986234949,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev192_s1_ul_mem : rev192_s1_ul.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane44 rev192_vertex0 rev192_vertex5 rev192_s1_ul
    rev192_vertex0_mem rev192_vertex5_mem (by decide)
def rev192_s1_ur : FractionPoint := ⟨116004500953,483892000000,13279497179665187,17172649631200000⟩
theorem rev192_s1_ur_mem : rev192_s1_ur.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane44 rev192_vertex0 rev192_vertex5 rev192_s1_ur
    rev192_vertex0_mem rev192_vertex5_mem (by decide)
theorem rev192_slab1 (p : Point) (hp : p∈IntegerCarrier rev192_planes)
    (hx0 : rev192_s1_ll.real.1≤p.1) (hx1 : p.1≤rev192_s1_lr.real.1) :
    p∈rationalHull (fractionRow192.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev192_plane12 rev192_plane44 rev192_s1_ll rev192_s1_lr rev192_s1_ul rev192_s1_ur
    (by decide) rev192_s1_ll_mem rev192_s1_lr_mem rev192_s1_ul_mem rev192_s1_ur_mem p
    (hp _ rev192_plane12_mem) (hp _ rev192_plane44_mem) hx0 hx1
def rev192_s2_ll : FractionPoint := ⟨116004500953,483892000000,367887499047,483892000000⟩
theorem rev192_s2_ll_mem : rev192_s2_ll.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane66 rev192_vertex2 rev192_vertex3 rev192_s2_ll
    rev192_vertex2_mem rev192_vertex3_mem (by decide)
def rev192_s2_lr : FractionPoint := ⟨79198296098933,296192993000000,450550071503799206391,609580581629636000000⟩
theorem rev192_s2_lr_mem : rev192_s2_lr.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane66 rev192_vertex2 rev192_vertex3 rev192_s2_lr
    rev192_vertex2_mem rev192_vertex3_mem (by decide)
def rev192_s2_ul : FractionPoint := ⟨116004500953,483892000000,13279497179665187,17172649631200000⟩
theorem rev192_s2_ul_mem : rev192_s2_ul.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane44 rev192_vertex0 rev192_vertex5 rev192_s2_ul
    rev192_vertex0_mem rev192_vertex5_mem (by decide)
def rev192_s2_ur : FractionPoint := ⟨79198296098933,296192993000000,1642088682618057,2073350951000000⟩
theorem rev192_s2_ur_mem : rev192_s2_ur.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane44 rev192_vertex0 rev192_vertex5 rev192_s2_ur
    rev192_vertex0_mem rev192_vertex5_mem (by decide)
theorem rev192_slab2 (p : Point) (hp : p∈IntegerCarrier rev192_planes)
    (hx0 : rev192_s2_ll.real.1≤p.1) (hx1 : p.1≤rev192_s2_lr.real.1) :
    p∈rationalHull (fractionRow192.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev192_plane66 rev192_plane44 rev192_s2_ll rev192_s2_lr rev192_s2_ul rev192_s2_ur
    (by decide) rev192_s2_ll_mem rev192_s2_lr_mem rev192_s2_ul_mem rev192_s2_ur_mem p
    (hp _ rev192_plane66_mem) (hp _ rev192_plane44_mem) hx0 hx1
def rev192_s3_ll : FractionPoint := ⟨79198296098933,296192993000000,450550071503799206391,609580581629636000000⟩
theorem rev192_s3_ll_mem : rev192_s3_ll.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane66 rev192_vertex2 rev192_vertex3 rev192_s3_ll
    rev192_vertex2_mem rev192_vertex3_mem (by decide)
def rev192_s3_lr : FractionPoint := ⟨314491167913198627,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev192_s3_lr_mem : rev192_s3_lr.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane66 rev192_vertex2 rev192_vertex3 rev192_s3_lr
    rev192_vertex2_mem rev192_vertex3_mem (by decide)
def rev192_s3_ul : FractionPoint := ⟨79198296098933,296192993000000,1642088682618057,2073350951000000⟩
theorem rev192_s3_ul_mem : rev192_s3_ul.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane48 rev192_vertex5 rev192_vertex4 rev192_s3_ul
    rev192_vertex5_mem rev192_vertex4_mem (by decide)
def rev192_s3_ur : FractionPoint := ⟨314491167913198627,1136108672356000000,1741065605883329761813,2206891096051530000000⟩
theorem rev192_s3_ur_mem : rev192_s3_ur.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane48 rev192_vertex5 rev192_vertex4 rev192_s3_ur
    rev192_vertex5_mem rev192_vertex4_mem (by decide)
theorem rev192_slab3 (p : Point) (hp : p∈IntegerCarrier rev192_planes)
    (hx0 : rev192_s3_ll.real.1≤p.1) (hx1 : p.1≤rev192_s3_lr.real.1) :
    p∈rationalHull (fractionRow192.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev192_plane66 rev192_plane48 rev192_s3_ll rev192_s3_lr rev192_s3_ul rev192_s3_ur
    (by decide) rev192_s3_ll_mem rev192_s3_lr_mem rev192_s3_ul_mem rev192_s3_ur_mem p
    (hp _ rev192_plane66_mem) (hp _ rev192_plane48_mem) hx0 hx1
def rev192_s4_ll : FractionPoint := ⟨314491167913198627,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev192_s4_ll_mem : rev192_s4_ll.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane70 rev192_vertex3 rev192_vertex4 rev192_s4_ll
    rev192_vertex3_mem rev192_vertex4_mem (by decide)
def rev192_s4_lr : FractionPoint := ⟨1862939987124017,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev192_s4_lr_mem : rev192_s4_lr.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane70 rev192_vertex3 rev192_vertex4 rev192_s4_lr
    rev192_vertex3_mem rev192_vertex4_mem (by decide)
def rev192_s4_ul : FractionPoint := ⟨314491167913198627,1136108672356000000,1741065605883329761813,2206891096051530000000⟩
theorem rev192_s4_ul_mem : rev192_s4_ul.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane48 rev192_vertex5 rev192_vertex4 rev192_s4_ul
    rev192_vertex5_mem rev192_vertex4_mem (by decide)
def rev192_s4_ur : FractionPoint := ⟨1862939987124017,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev192_s4_ur_mem : rev192_s4_ur.real ∈ rationalHull (fractionRow192.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow192 rev192_plane48 rev192_vertex5 rev192_vertex4 rev192_s4_ur
    rev192_vertex5_mem rev192_vertex4_mem (by decide)
theorem rev192_slab4 (p : Point) (hp : p∈IntegerCarrier rev192_planes)
    (hx0 : rev192_s4_ll.real.1≤p.1) (hx1 : p.1≤rev192_s4_lr.real.1) :
    p∈rationalHull (fractionRow192.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev192_plane70 rev192_plane48 rev192_s4_ll rev192_s4_lr rev192_s4_ul rev192_s4_ur
    (by decide) rev192_s4_ll_mem rev192_s4_lr_mem rev192_s4_ul_mem rev192_s4_ur_mem p
    (hp _ rev192_plane70_mem) (hp _ rev192_plane48_mem) hx0 hx1
theorem rev192_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev192_planes) : rev192_s0_ll.real.1≤p.1 := by
  have hc := rev192_plane12.combine_sound rev192_plane16 287616000000 1574160000000 (by decide) (by decide) p
    (hp _ rev192_plane12_mem) (hp _ rev192_plane16_mem)
  exact (rev192_plane12.combine rev192_plane16 287616000000 1574160000000).xBoundCheck_sound rev192_s0_ll.nx rev192_s0_ll.dx true (by decide) p hc
theorem rev192_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev192_planes) : p.1≤rev192_s4_lr.real.1 := by
  have hc := rev192_plane48.combine_sound rev192_plane70 2044968000000 2144520000000 (by decide) (by decide) p
    (hp _ rev192_plane48_mem) (hp _ rev192_plane70_mem)
  exact (rev192_plane48.combine rev192_plane70 2044968000000 2144520000000).xBoundCheck_sound rev192_s4_lr.nx rev192_s4_lr.dx false (by decide) p hc
theorem rev192_hull (p : Point) (hp : p∈IntegerCarrier rev192_planes) :
    p∈rationalHull (fractionRow192.map FractionPoint.rational) := by
  have hxlo := rev192_bound0_lo p hp
  have hxhi := rev192_bound0_hi p hp
  by_cases h0 : p.1≤rev192_s0_lr.real.1
  · exact rev192_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev192_s1_lr.real.1
  · exact rev192_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev192_s2_lr.real.1
  · exact rev192_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev192_s3_lr.real.1
  · exact rev192_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev192_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull192 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,10,5,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow192 := by
  rw [← fractionRow192_correct]
  exact rev192_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull192
