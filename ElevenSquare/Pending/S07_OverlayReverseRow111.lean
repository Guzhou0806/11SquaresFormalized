import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks13
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev111_planes : List IntegerPlane := integerOverlayPlanes ![8,10,5,2]
def rev111_plane13 : IntegerPlane := ⟨2044968000000,(-643972000000),82535475981⟩
theorem rev111_plane13_mem : rev111_plane13 ∈ rev111_planes := by decide
def rev111_plane17 : IntegerPlane := ⟨2058052000000,1574160000000,1690164500953⟩
theorem rev111_plane17_mem : rev111_plane17 ∈ rev111_planes := by decide
def rev111_plane35 : IntegerPlane := ⟨(-2144520000000),(-699568000000),(-958577891352)⟩
theorem rev111_plane35_mem : rev111_plane35 ∈ rev111_planes := by decide
def rev111_plane39 : IntegerPlane := ⟨(-2129316000000),1440116000000,612143880216⟩
theorem rev111_plane39_mem : rev111_plane39 ∈ rev111_planes := by decide
def rev111_plane67 : IntegerPlane := ⟨(-287616000000),1855520000000,1356143759600⟩
theorem rev111_plane67_mem : rev111_plane67 ∈ rev111_planes := by decide
def rev111_plane71 : IntegerPlane := ⟨1574160000000,2058052000000,1942047499047⟩
theorem rev111_plane71_mem : rev111_plane71 ∈ rev111_planes := by decide
def rev111_vertex0 : FractionPoint := fractionRow111[0]!
theorem rev111_vertex0_mem : rev111_vertex0∈fractionRow111 := by decide
def rev111_vertex1 : FractionPoint := fractionRow111[1]!
theorem rev111_vertex1_mem : rev111_vertex1∈fractionRow111 := by decide
def rev111_vertex2 : FractionPoint := fractionRow111[2]!
theorem rev111_vertex2_mem : rev111_vertex2∈fractionRow111 := by decide
def rev111_vertex3 : FractionPoint := fractionRow111[3]!
theorem rev111_vertex3_mem : rev111_vertex3∈fractionRow111 := by decide
def rev111_vertex4 : FractionPoint := fractionRow111[4]!
theorem rev111_vertex4_mem : rev111_vertex4∈fractionRow111 := by decide
def rev111_vertex5 : FractionPoint := fractionRow111[5]!
theorem rev111_vertex5_mem : rev111_vertex5∈fractionRow111 := by decide
def rev111_s0_ll : FractionPoint := ⟨431262268381943,2073350951000000,216994696901067,296192993000000⟩
theorem rev111_s0_ll_mem : rev111_s0_ll.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane35 rev111_vertex5 rev111_vertex0 rev111_s0_ll
    rev111_vertex5_mem rev111_vertex0_mem (by decide)
def rev111_s0_lr : FractionPoint := ⟨2553622230880379,11052462565200000,6623126699571354093,10005110160212000000⟩
theorem rev111_s0_lr_mem : rev111_s0_lr.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane35 rev111_vertex5 rev111_vertex0 rev111_s0_lr
    rev111_vertex5_mem rev111_vertex0_mem (by decide)
def rev111_s0_ul : FractionPoint := ⟨431262268381943,2073350951000000,216994696901067,296192993000000⟩
theorem rev111_s0_ul_mem : rev111_s0_ul.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane39 rev111_vertex5 rev111_vertex4 rev111_s0_ul
    rev111_vertex5_mem rev111_vertex4_mem (by decide)
def rev111_s0_ur : FractionPoint := ⟨2553622230880379,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev111_s0_ur_mem : rev111_s0_ur.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane39 rev111_vertex5 rev111_vertex4 rev111_s0_ur
    rev111_vertex5_mem rev111_vertex4_mem (by decide)
theorem rev111_slab0 (p : Point) (hp : p∈IntegerCarrier rev111_planes)
    (hx0 : rev111_s0_ll.real.1≤p.1) (hx1 : p.1≤rev111_s0_lr.real.1) :
    p∈rationalHull (fractionRow111.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev111_plane35 rev111_plane39 rev111_s0_ll rev111_s0_lr rev111_s0_ul rev111_s0_ur
    (by decide) rev111_s0_ll_mem rev111_s0_lr_mem rev111_s0_ul_mem rev111_s0_ur_mem p
    (hp _ rev111_plane35_mem) (hp _ rev111_plane39_mem) hx0 hx1
def rev111_s1_ll : FractionPoint := ⟨2553622230880379,11052462565200000,6623126699571354093,10005110160212000000⟩
theorem rev111_s1_ll_mem : rev111_s1_ll.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane35 rev111_vertex5 rev111_vertex0 rev111_s1_ll
    rev111_vertex5_mem rev111_vertex0_mem (by decide)
def rev111_s1_lr : FractionPoint := ⟨5078084991871189,21955087795200000,13141313323503163293,19874581856512000000⟩
theorem rev111_s1_lr_mem : rev111_s1_lr.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane35 rev111_vertex5 rev111_vertex0 rev111_s1_lr
    rev111_vertex5_mem rev111_vertex0_mem (by decide)
def rev111_s1_ul : FractionPoint := ⟨2553622230880379,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev111_s1_ul_mem : rev111_s1_ul.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane67 rev111_vertex4 rev111_vertex3 rev111_s1_ul
    rev111_vertex4_mem rev111_vertex3_mem (by decide)
def rev111_s1_ur : FractionPoint := ⟨5078084991871189,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev111_s1_ur_mem : rev111_s1_ur.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane67 rev111_vertex4 rev111_vertex3 rev111_s1_ur
    rev111_vertex4_mem rev111_vertex3_mem (by decide)
theorem rev111_slab1 (p : Point) (hp : p∈IntegerCarrier rev111_planes)
    (hx0 : rev111_s1_ll.real.1≤p.1) (hx1 : p.1≤rev111_s1_lr.real.1) :
    p∈rationalHull (fractionRow111.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev111_plane35 rev111_plane67 rev111_s1_ll rev111_s1_lr rev111_s1_ul rev111_s1_ur
    (by decide) rev111_s1_ll_mem rev111_s1_lr_mem rev111_s1_ul_mem rev111_s1_ur_mem p
    (hp _ rev111_plane35_mem) (hp _ rev111_plane67_mem) hx0 hx1
def rev111_s2_ll : FractionPoint := ⟨5078084991871189,21955087795200000,13141313323503163293,19874581856512000000⟩
theorem rev111_s2_ll_mem : rev111_s2_ll.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane35 rev111_vertex5 rev111_vertex0 rev111_s2_ll
    rev111_vertex5_mem rev111_vertex0_mem (by decide)
def rev111_s2_lr : FractionPoint := ⟨116004500953,483892000000,1168881525099861,1839757384000000⟩
theorem rev111_s2_lr_mem : rev111_s2_lr.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane35 rev111_vertex5 rev111_vertex0 rev111_s2_lr
    rev111_vertex5_mem rev111_vertex0_mem (by decide)
def rev111_s2_ul : FractionPoint := ⟨5078084991871189,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev111_s2_ul_mem : rev111_s2_ul.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane71 rev111_vertex3 rev111_vertex2 rev111_s2_ul
    rev111_vertex3_mem rev111_vertex2_mem (by decide)
def rev111_s2_ur : FractionPoint := ⟨116004500953,483892000000,367887499047,483892000000⟩
theorem rev111_s2_ur_mem : rev111_s2_ur.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane71 rev111_vertex3 rev111_vertex2 rev111_s2_ur
    rev111_vertex3_mem rev111_vertex2_mem (by decide)
theorem rev111_slab2 (p : Point) (hp : p∈IntegerCarrier rev111_planes)
    (hx0 : rev111_s2_ll.real.1≤p.1) (hx1 : p.1≤rev111_s2_lr.real.1) :
    p∈rationalHull (fractionRow111.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev111_plane35 rev111_plane71 rev111_s2_ll rev111_s2_lr rev111_s2_ul rev111_s2_ur
    (by decide) rev111_s2_ll_mem rev111_s2_lr_mem rev111_s2_ul_mem rev111_s2_ur_mem p
    (hp _ rev111_plane35_mem) (hp _ rev111_plane71_mem) hx0 hx1
def rev111_s3_ll : FractionPoint := ⟨116004500953,483892000000,1168881525099861,1839757384000000⟩
theorem rev111_s3_ll_mem : rev111_s3_ll.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane35 rev111_vertex5 rev111_vertex0 rev111_s3_ll
    rev111_vertex5_mem rev111_vertex0_mem (by decide)
def rev111_s3_lr : FractionPoint := ⟨611446104810513,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev111_s3_lr_mem : rev111_s3_lr.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane35 rev111_vertex5 rev111_vertex0 rev111_s3_lr
    rev111_vertex5_mem rev111_vertex0_mem (by decide)
def rev111_s3_ul : FractionPoint := ⟨116004500953,483892000000,367887499047,483892000000⟩
theorem rev111_s3_ul_mem : rev111_s3_ul.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane17 rev111_vertex2 rev111_vertex1 rev111_s3_ul
    rev111_vertex2_mem rev111_vertex1_mem (by decide)
def rev111_s3_ur : FractionPoint := ⟨611446104810513,2546743666000000,1523013929201308906511,2004491004635280000000⟩
theorem rev111_s3_ur_mem : rev111_s3_ur.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane17 rev111_vertex2 rev111_vertex1 rev111_s3_ur
    rev111_vertex2_mem rev111_vertex1_mem (by decide)
theorem rev111_slab3 (p : Point) (hp : p∈IntegerCarrier rev111_planes)
    (hx0 : rev111_s3_ll.real.1≤p.1) (hx1 : p.1≤rev111_s3_lr.real.1) :
    p∈rationalHull (fractionRow111.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev111_plane35 rev111_plane17 rev111_s3_ll rev111_s3_lr rev111_s3_ul rev111_s3_ur
    (by decide) rev111_s3_ll_mem rev111_s3_lr_mem rev111_s3_ul_mem rev111_s3_ur_mem p
    (hp _ rev111_plane35_mem) (hp _ rev111_plane17_mem) hx0 hx1
def rev111_s4_ll : FractionPoint := ⟨611446104810513,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev111_s4_ll_mem : rev111_s4_ll.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane13 rev111_vertex0 rev111_vertex1 rev111_s4_ll
    rev111_vertex0_mem rev111_vertex1_mem (by decide)
def rev111_s4_lr : FractionPoint := ⟨43512237817069867,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev111_s4_lr_mem : rev111_s4_lr.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane13 rev111_vertex0 rev111_vertex1 rev111_s4_lr
    rev111_vertex0_mem rev111_vertex1_mem (by decide)
def rev111_s4_ul : FractionPoint := ⟨611446104810513,2546743666000000,1523013929201308906511,2004491004635280000000⟩
theorem rev111_s4_ul_mem : rev111_s4_ul.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane17 rev111_vertex2 rev111_vertex1 rev111_s4_ul
    rev111_vertex2_mem rev111_vertex1_mem (by decide)
def rev111_s4_ur : FractionPoint := ⟨43512237817069867,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev111_s4_ur_mem : rev111_s4_ur.real ∈ rationalHull (fractionRow111.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow111 rev111_plane17 rev111_vertex2 rev111_vertex1 rev111_s4_ur
    rev111_vertex2_mem rev111_vertex1_mem (by decide)
theorem rev111_slab4 (p : Point) (hp : p∈IntegerCarrier rev111_planes)
    (hx0 : rev111_s4_ll.real.1≤p.1) (hx1 : p.1≤rev111_s4_lr.real.1) :
    p∈rationalHull (fractionRow111.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev111_plane13 rev111_plane17 rev111_s4_ll rev111_s4_lr rev111_s4_ul rev111_s4_ur
    (by decide) rev111_s4_ll_mem rev111_s4_lr_mem rev111_s4_ul_mem rev111_s4_ur_mem p
    (hp _ rev111_plane13_mem) (hp _ rev111_plane17_mem) hx0 hx1
theorem rev111_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev111_planes) : rev111_s0_ll.real.1≤p.1 := by
  have hc := rev111_plane35.combine_sound rev111_plane39 1440116000000 699568000000 (by decide) (by decide) p
    (hp _ rev111_plane35_mem) (hp _ rev111_plane39_mem)
  exact (rev111_plane35.combine rev111_plane39 1440116000000 699568000000).xBoundCheck_sound rev111_s0_ll.nx rev111_s0_ll.dx true (by decide) p hc
theorem rev111_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev111_planes) : p.1≤rev111_s4_lr.real.1 := by
  have hc := rev111_plane13.combine_sound rev111_plane17 1574160000000 643972000000 (by decide) (by decide) p
    (hp _ rev111_plane13_mem) (hp _ rev111_plane17_mem)
  exact (rev111_plane13.combine rev111_plane17 1574160000000 643972000000).xBoundCheck_sound rev111_s4_lr.nx rev111_s4_lr.dx false (by decide) p hc
theorem rev111_hull (p : Point) (hp : p∈IntegerCarrier rev111_planes) :
    p∈rationalHull (fractionRow111.map FractionPoint.rational) := by
  have hxlo := rev111_bound0_lo p hp
  have hxhi := rev111_bound0_hi p hp
  by_cases h0 : p.1≤rev111_s0_lr.real.1
  · exact rev111_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev111_s1_lr.real.1
  · exact rev111_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev111_s2_lr.real.1
  · exact rev111_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev111_s3_lr.real.1
  · exact rev111_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev111_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull111 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,10,5,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow111 := by
  rw [← fractionRow111_correct]
  exact rev111_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull111
