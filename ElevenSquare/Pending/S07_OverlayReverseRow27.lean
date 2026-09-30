import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks3
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev27_planes : List IntegerPlane := integerOverlayPlanes ![2,5,10,8]
def rev27_plane7 : IntegerPlane := ⟨1855520000000,(-287616000000),1356143759600⟩
theorem rev27_plane7_mem : rev27_plane7 ∈ rev27_planes := by decide
def rev27_plane11 : IntegerPlane := ⟨2058052000000,1574160000000,1942047499047⟩
theorem rev27_plane11_mem : rev27_plane11 ∈ rev27_planes := by decide
def rev27_plane55 : IntegerPlane := ⟨(-699568000000),(-2144520000000),(-958577891352)⟩
theorem rev27_plane55_mem : rev27_plane55 ∈ rev27_planes := by decide
def rev27_plane59 : IntegerPlane := ⟨1440116000000,(-2129316000000),612143880216⟩
theorem rev27_plane59_mem : rev27_plane59 ∈ rev27_planes := by decide
def rev27_plane73 : IntegerPlane := ⟨(-643972000000),2044968000000,82535475981⟩
theorem rev27_plane73_mem : rev27_plane73 ∈ rev27_planes := by decide
def rev27_plane77 : IntegerPlane := ⟨1574160000000,2058052000000,1690164500953⟩
theorem rev27_plane77_mem : rev27_plane77 ∈ rev27_planes := by decide
def rev27_vertex0 : FractionPoint := fractionRow27[0]!
theorem rev27_vertex0_mem : rev27_vertex0∈fractionRow27 := by decide
def rev27_vertex1 : FractionPoint := fractionRow27[1]!
theorem rev27_vertex1_mem : rev27_vertex1∈fractionRow27 := by decide
def rev27_vertex2 : FractionPoint := fractionRow27[2]!
theorem rev27_vertex2_mem : rev27_vertex2∈fractionRow27 := by decide
def rev27_vertex3 : FractionPoint := fractionRow27[3]!
theorem rev27_vertex3_mem : rev27_vertex3∈fractionRow27 := by decide
def rev27_vertex4 : FractionPoint := fractionRow27[4]!
theorem rev27_vertex4_mem : rev27_vertex4∈fractionRow27 := by decide
def rev27_vertex5 : FractionPoint := fractionRow27[5]!
theorem rev27_vertex5_mem : rev27_vertex5∈fractionRow27 := by decide
def rev27_s0_ll : FractionPoint := ⟨3230547344875983,5093487332000000,611446104810513,2546743666000000⟩
theorem rev27_s0_ll_mem : rev27_s0_ll.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane55 rev27_vertex4 rev27_vertex5 rev27_s0_ll
    rev27_vertex4_mem rev27_vertex5_mem (by decide)
def rev27_s0_lr : FractionPoint := ⟨821617504442801373,1136108672356000000,465825490168200238187,2206891096051530000000⟩
theorem rev27_s0_lr_mem : rev27_s0_lr.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane55 rev27_vertex4 rev27_vertex5 rev27_s0_lr
    rev27_vertex4_mem rev27_vertex5_mem (by decide)
def rev27_s0_ul : FractionPoint := ⟨3230547344875983,5093487332000000,611446104810513,2546743666000000⟩
theorem rev27_s0_ul_mem : rev27_s0_ul.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane73 rev27_vertex4 rev27_vertex3 rev27_s0_ul
    rev27_vertex4_mem rev27_vertex3_mem (by decide)
def rev27_s0_ur : FractionPoint := ⟨821617504442801373,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev27_s0_ur_mem : rev27_s0_ur.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane73 rev27_vertex4 rev27_vertex3 rev27_s0_ur
    rev27_vertex4_mem rev27_vertex3_mem (by decide)
theorem rev27_slab0 (p : Point) (hp : p∈IntegerCarrier rev27_planes)
    (hx0 : rev27_s0_ll.real.1≤p.1) (hx1 : p.1≤rev27_s0_lr.real.1) :
    p∈rationalHull (fractionRow27.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev27_plane55 rev27_plane73 rev27_s0_ll rev27_s0_lr rev27_s0_ul rev27_s0_ur
    (by decide) rev27_s0_ll_mem rev27_s0_lr_mem rev27_s0_ul_mem rev27_s0_ur_mem p
    (hp _ rev27_plane55_mem) (hp _ rev27_plane73_mem) hx0 hx1
def rev27_s1_ll : FractionPoint := ⟨821617504442801373,1136108672356000000,465825490168200238187,2206891096051530000000⟩
theorem rev27_s1_ll_mem : rev27_s1_ll.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane55 rev27_vertex4 rev27_vertex5 rev27_s1_ll
    rev27_vertex4_mem rev27_vertex5_mem (by decide)
def rev27_s1_lr : FractionPoint := ⟨216994696901067,296192993000000,431262268381943,2073350951000000⟩
theorem rev27_s1_lr_mem : rev27_s1_lr.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane55 rev27_vertex4 rev27_vertex5 rev27_s1_lr
    rev27_vertex4_mem rev27_vertex5_mem (by decide)
def rev27_s1_ul : FractionPoint := ⟨821617504442801373,1136108672356000000,43512237817069867,162301238908000000⟩
theorem rev27_s1_ul_mem : rev27_s1_ul.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane77 rev27_vertex3 rev27_vertex2 rev27_s1_ul
    rev27_vertex3_mem rev27_vertex2_mem (by decide)
def rev27_s1_ur : FractionPoint := ⟨216994696901067,296192993000000,159030510125836793609,609580581629636000000⟩
theorem rev27_s1_ur_mem : rev27_s1_ur.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane77 rev27_vertex3 rev27_vertex2 rev27_s1_ur
    rev27_vertex3_mem rev27_vertex2_mem (by decide)
theorem rev27_slab1 (p : Point) (hp : p∈IntegerCarrier rev27_planes)
    (hx0 : rev27_s1_ll.real.1≤p.1) (hx1 : p.1≤rev27_s1_lr.real.1) :
    p∈rationalHull (fractionRow27.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev27_plane55 rev27_plane77 rev27_s1_ll rev27_s1_lr rev27_s1_ul rev27_s1_ur
    (by decide) rev27_s1_ll_mem rev27_s1_lr_mem rev27_s1_ul_mem rev27_s1_ur_mem p
    (hp _ rev27_plane55_mem) (hp _ rev27_plane77_mem) hx0 hx1
def rev27_s2_ll : FractionPoint := ⟨216994696901067,296192993000000,431262268381943,2073350951000000⟩
theorem rev27_s2_ll_mem : rev27_s2_ll.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane59 rev27_vertex5 rev27_vertex0 rev27_s2_ll
    rev27_vertex5_mem rev27_vertex0_mem (by decide)
def rev27_s2_lr : FractionPoint := ⟨367887499047,483892000000,3893152451534813,17172649631200000⟩
theorem rev27_s2_lr_mem : rev27_s2_lr.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane59 rev27_vertex5 rev27_vertex0 rev27_s2_lr
    rev27_vertex5_mem rev27_vertex0_mem (by decide)
def rev27_s2_ul : FractionPoint := ⟨216994696901067,296192993000000,159030510125836793609,609580581629636000000⟩
theorem rev27_s2_ul_mem : rev27_s2_ul.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane77 rev27_vertex3 rev27_vertex2 rev27_s2_ul
    rev27_vertex3_mem rev27_vertex2_mem (by decide)
def rev27_s2_ur : FractionPoint := ⟨367887499047,483892000000,116004500953,483892000000⟩
theorem rev27_s2_ur_mem : rev27_s2_ur.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane77 rev27_vertex3 rev27_vertex2 rev27_s2_ur
    rev27_vertex3_mem rev27_vertex2_mem (by decide)
theorem rev27_slab2 (p : Point) (hp : p∈IntegerCarrier rev27_planes)
    (hx0 : rev27_s2_ll.real.1≤p.1) (hx1 : p.1≤rev27_s2_lr.real.1) :
    p∈rationalHull (fractionRow27.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev27_plane59 rev27_plane77 rev27_s2_ll rev27_s2_lr rev27_s2_ul rev27_s2_ur
    (by decide) rev27_s2_ll_mem rev27_s2_lr_mem rev27_s2_ul_mem rev27_s2_ur_mem p
    (hp _ rev27_plane59_mem) (hp _ rev27_plane77_mem) hx0 hx1
def rev27_s3_ll : FractionPoint := ⟨367887499047,483892000000,3893152451534813,17172649631200000⟩
theorem rev27_s3_ll_mem : rev27_s3_ll.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane59 rev27_vertex5 rev27_vertex0 rev27_s3_ll
    rev27_vertex5_mem rev27_vertex0_mem (by decide)
def rev27_s3_lr : FractionPoint := ⟨2017556719765051,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev27_s3_lr_mem : rev27_s3_lr.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane59 rev27_vertex5 rev27_vertex0 rev27_s3_lr
    rev27_vertex5_mem rev27_vertex0_mem (by decide)
def rev27_s3_ul : FractionPoint := ⟨367887499047,483892000000,116004500953,483892000000⟩
theorem rev27_s3_ul_mem : rev27_s3_ul.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane11 rev27_vertex2 rev27_vertex1 rev27_s3_ul
    rev27_vertex2_mem rev27_vertex1_mem (by decide)
def rev27_s3_ur : FractionPoint := ⟨2017556719765051,2631538706000000,13690521720096798179,59178042420528000000⟩
theorem rev27_s3_ur_mem : rev27_s3_ur.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane11 rev27_vertex2 rev27_vertex1 rev27_s3_ur
    rev27_vertex2_mem rev27_vertex1_mem (by decide)
theorem rev27_slab3 (p : Point) (hp : p∈IntegerCarrier rev27_planes)
    (hx0 : rev27_s3_ll.real.1≤p.1) (hx1 : p.1≤rev27_s3_lr.real.1) :
    p∈rationalHull (fractionRow27.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev27_plane59 rev27_plane11 rev27_s3_ll rev27_s3_lr rev27_s3_ul rev27_s3_ur
    (by decide) rev27_s3_ll_mem rev27_s3_lr_mem rev27_s3_ul_mem rev27_s3_ur_mem p
    (hp _ rev27_plane59_mem) (hp _ rev27_plane11_mem) hx0 hx1
def rev27_s4_ll : FractionPoint := ⟨2017556719765051,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev27_s4_ll_mem : rev27_s4_ll.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane7 rev27_vertex0 rev27_vertex1 rev27_s4_ll
    rev27_vertex0_mem rev27_vertex1_mem (by decide)
def rev27_s4_lr : FractionPoint := ⟨1001990771613779,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev27_s4_lr_mem : rev27_s4_lr.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane7 rev27_vertex0 rev27_vertex1 rev27_s4_lr
    rev27_vertex0_mem rev27_vertex1_mem (by decide)
def rev27_s4_ul : FractionPoint := ⟨2017556719765051,2631538706000000,13690521720096798179,59178042420528000000⟩
theorem rev27_s4_ul_mem : rev27_s4_ul.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane11 rev27_vertex2 rev27_vertex1 rev27_s4_ul
    rev27_vertex2_mem rev27_vertex1_mem (by decide)
def rev27_s4_ur : FractionPoint := ⟨1001990771613779,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev27_s4_ur_mem : rev27_s4_ur.real ∈ rationalHull (fractionRow27.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow27 rev27_plane11 rev27_vertex2 rev27_vertex1 rev27_s4_ur
    rev27_vertex2_mem rev27_vertex1_mem (by decide)
theorem rev27_slab4 (p : Point) (hp : p∈IntegerCarrier rev27_planes)
    (hx0 : rev27_s4_ll.real.1≤p.1) (hx1 : p.1≤rev27_s4_lr.real.1) :
    p∈rationalHull (fractionRow27.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev27_plane7 rev27_plane11 rev27_s4_ll rev27_s4_lr rev27_s4_ul rev27_s4_ur
    (by decide) rev27_s4_ll_mem rev27_s4_lr_mem rev27_s4_ul_mem rev27_s4_ur_mem p
    (hp _ rev27_plane7_mem) (hp _ rev27_plane11_mem) hx0 hx1
theorem rev27_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev27_planes) : rev27_s0_ll.real.1≤p.1 := by
  have hc := rev27_plane55.combine_sound rev27_plane73 2044968000000 2144520000000 (by decide) (by decide) p
    (hp _ rev27_plane55_mem) (hp _ rev27_plane73_mem)
  exact (rev27_plane55.combine rev27_plane73 2044968000000 2144520000000).xBoundCheck_sound rev27_s0_ll.nx rev27_s0_ll.dx true (by decide) p hc
theorem rev27_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev27_planes) : p.1≤rev27_s4_lr.real.1 := by
  have hc := rev27_plane7.combine_sound rev27_plane11 1574160000000 287616000000 (by decide) (by decide) p
    (hp _ rev27_plane7_mem) (hp _ rev27_plane11_mem)
  exact (rev27_plane7.combine rev27_plane11 1574160000000 287616000000).xBoundCheck_sound rev27_s4_lr.nx rev27_s4_lr.dx false (by decide) p hc
theorem rev27_hull (p : Point) (hp : p∈IntegerCarrier rev27_planes) :
    p∈rationalHull (fractionRow27.map FractionPoint.rational) := by
  have hxlo := rev27_bound0_lo p hp
  have hxhi := rev27_bound0_hi p hp
  by_cases h0 : p.1≤rev27_s0_lr.real.1
  · exact rev27_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev27_s1_lr.real.1
  · exact rev27_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev27_s2_lr.real.1
  · exact rev27_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev27_s3_lr.real.1
  · exact rev27_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev27_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull27 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,5,10,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow27 := by
  rw [← fractionRow27_correct]
  exact rev27_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull27
