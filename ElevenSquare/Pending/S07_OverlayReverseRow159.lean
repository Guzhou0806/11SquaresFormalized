import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks19
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev159_planes : List IntegerPlane := integerOverlayPlanes ![10,13,8,10]
def rev159_plane32 : IntegerPlane := ⟨2058052000000,(-1574160000000),367887499047⟩
theorem rev159_plane32_mem : rev159_plane32 ∈ rev159_planes := by decide
def rev159_plane36 : IntegerPlane := ⟨1855520000000,287616000000,1643759759600⟩
theorem rev159_plane36_mem : rev159_plane36 ∈ rev159_planes := by decide
def rev159_plane53 : IntegerPlane := ⟨(-643972000000),(-2044968000000),(-1962432524019)⟩
theorem rev159_plane53_mem : rev159_plane53 ∈ rev159_planes := by decide
def rev159_plane57 : IntegerPlane := ⟨1574160000000,(-2058052000000),(-367887499047)⟩
theorem rev159_plane57_mem : rev159_plane57 ∈ rev159_planes := by decide
def rev159_plane75 : IntegerPlane := ⟨(-699568000000),2144520000000,1185942108648⟩
theorem rev159_plane75_mem : rev159_plane75 ∈ rev159_planes := by decide
def rev159_plane79 : IntegerPlane := ⟨1440116000000,2129316000000,2741459880216⟩
theorem rev159_plane79_mem : rev159_plane79 ∈ rev159_planes := by decide
def rev159_vertex0 : FractionPoint := fractionRow159[0]!
theorem rev159_vertex0_mem : rev159_vertex0∈fractionRow159 := by decide
def rev159_vertex1 : FractionPoint := fractionRow159[1]!
theorem rev159_vertex1_mem : rev159_vertex1∈fractionRow159 := by decide
def rev159_vertex2 : FractionPoint := fractionRow159[2]!
theorem rev159_vertex2_mem : rev159_vertex2∈fractionRow159 := by decide
def rev159_vertex3 : FractionPoint := fractionRow159[3]!
theorem rev159_vertex3_mem : rev159_vertex3∈fractionRow159 := by decide
def rev159_vertex4 : FractionPoint := fractionRow159[4]!
theorem rev159_vertex4_mem : rev159_vertex4∈fractionRow159 := by decide
def rev159_vertex5 : FractionPoint := fractionRow159[5]!
theorem rev159_vertex5_mem : rev159_vertex5∈fractionRow159 := by decide
def rev159_s0_ll : FractionPoint := ⟨3230547344875983,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev159_s0_ll_mem : rev159_s0_ll.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane53 rev159_vertex4 rev159_vertex5 rev159_s0_ll
    rev159_vertex4_mem rev159_vertex5_mem (by decide)
def rev159_s0_lr : FractionPoint := ⟨821617504442801373,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev159_s0_lr_mem : rev159_s0_lr.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane53 rev159_vertex4 rev159_vertex5 rev159_s0_lr
    rev159_vertex4_mem rev159_vertex5_mem (by decide)
def rev159_s0_ul : FractionPoint := ⟨3230547344875983,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev159_s0_ul_mem : rev159_s0_ul.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane75 rev159_vertex4 rev159_vertex3 rev159_s0_ul
    rev159_vertex4_mem rev159_vertex3_mem (by decide)
def rev159_s0_ur : FractionPoint := ⟨821617504442801373,1136108672356000000,1741065605883329761813,2206891096051530000000⟩
theorem rev159_s0_ur_mem : rev159_s0_ur.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane75 rev159_vertex4 rev159_vertex3 rev159_s0_ur
    rev159_vertex4_mem rev159_vertex3_mem (by decide)
theorem rev159_slab0 (p : Point) (hp : p∈IntegerCarrier rev159_planes)
    (hx0 : rev159_s0_ll.real.1≤p.1) (hx1 : p.1≤rev159_s0_lr.real.1) :
    p∈rationalHull (fractionRow159.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev159_plane53 rev159_plane75 rev159_s0_ll rev159_s0_lr rev159_s0_ul rev159_s0_ur
    (by decide) rev159_s0_ll_mem rev159_s0_lr_mem rev159_s0_ul_mem rev159_s0_ur_mem p
    (hp _ rev159_plane53_mem) (hp _ rev159_plane75_mem) hx0 hx1
def rev159_s1_ll : FractionPoint := ⟨821617504442801373,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev159_s1_ll_mem : rev159_s1_ll.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane57 rev159_vertex5 rev159_vertex0 rev159_s1_ll
    rev159_vertex5_mem rev159_vertex0_mem (by decide)
def rev159_s1_lr : FractionPoint := ⟨216994696901067,296192993000000,450550071503799206391,609580581629636000000⟩
theorem rev159_s1_lr_mem : rev159_s1_lr.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane57 rev159_vertex5 rev159_vertex0 rev159_s1_lr
    rev159_vertex5_mem rev159_vertex0_mem (by decide)
def rev159_s1_ul : FractionPoint := ⟨821617504442801373,1136108672356000000,1741065605883329761813,2206891096051530000000⟩
theorem rev159_s1_ul_mem : rev159_s1_ul.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane75 rev159_vertex4 rev159_vertex3 rev159_s1_ul
    rev159_vertex4_mem rev159_vertex3_mem (by decide)
def rev159_s1_ur : FractionPoint := ⟨216994696901067,296192993000000,1642088682618057,2073350951000000⟩
theorem rev159_s1_ur_mem : rev159_s1_ur.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane75 rev159_vertex4 rev159_vertex3 rev159_s1_ur
    rev159_vertex4_mem rev159_vertex3_mem (by decide)
theorem rev159_slab1 (p : Point) (hp : p∈IntegerCarrier rev159_planes)
    (hx0 : rev159_s1_ll.real.1≤p.1) (hx1 : p.1≤rev159_s1_lr.real.1) :
    p∈rationalHull (fractionRow159.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev159_plane57 rev159_plane75 rev159_s1_ll rev159_s1_lr rev159_s1_ul rev159_s1_ur
    (by decide) rev159_s1_ll_mem rev159_s1_lr_mem rev159_s1_ul_mem rev159_s1_ur_mem p
    (hp _ rev159_plane57_mem) (hp _ rev159_plane75_mem) hx0 hx1
def rev159_s2_ll : FractionPoint := ⟨216994696901067,296192993000000,450550071503799206391,609580581629636000000⟩
theorem rev159_s2_ll_mem : rev159_s2_ll.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane57 rev159_vertex5 rev159_vertex0 rev159_s2_ll
    rev159_vertex5_mem rev159_vertex0_mem (by decide)
def rev159_s2_lr : FractionPoint := ⟨367887499047,483892000000,367887499047,483892000000⟩
theorem rev159_s2_lr_mem : rev159_s2_lr.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane57 rev159_vertex5 rev159_vertex0 rev159_s2_lr
    rev159_vertex5_mem rev159_vertex0_mem (by decide)
def rev159_s2_ul : FractionPoint := ⟨216994696901067,296192993000000,1642088682618057,2073350951000000⟩
theorem rev159_s2_ul_mem : rev159_s2_ul.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane79 rev159_vertex3 rev159_vertex2 rev159_s2_ul
    rev159_vertex3_mem rev159_vertex2_mem (by decide)
def rev159_s2_ur : FractionPoint := ⟨367887499047,483892000000,13279497179665187,17172649631200000⟩
theorem rev159_s2_ur_mem : rev159_s2_ur.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane79 rev159_vertex3 rev159_vertex2 rev159_s2_ur
    rev159_vertex3_mem rev159_vertex2_mem (by decide)
theorem rev159_slab2 (p : Point) (hp : p∈IntegerCarrier rev159_planes)
    (hx0 : rev159_s2_ll.real.1≤p.1) (hx1 : p.1≤rev159_s2_lr.real.1) :
    p∈rationalHull (fractionRow159.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev159_plane57 rev159_plane79 rev159_s2_ll rev159_s2_lr rev159_s2_ul rev159_s2_ur
    (by decide) rev159_s2_ll_mem rev159_s2_lr_mem rev159_s2_ul_mem rev159_s2_ur_mem p
    (hp _ rev159_plane57_mem) (hp _ rev159_plane79_mem) hx0 hx1
def rev159_s3_ll : FractionPoint := ⟨367887499047,483892000000,367887499047,483892000000⟩
theorem rev159_s3_ll_mem : rev159_s3_ll.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane32 rev159_vertex0 rev159_vertex1 rev159_s3_ll
    rev159_vertex0_mem rev159_vertex1_mem (by decide)
def rev159_s3_lr : FractionPoint := ⟨2017556719765051,2631538706000000,45487520700431201821,59178042420528000000⟩
theorem rev159_s3_lr_mem : rev159_s3_lr.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane32 rev159_vertex0 rev159_vertex1 rev159_s3_lr
    rev159_vertex0_mem rev159_vertex1_mem (by decide)
def rev159_s3_ul : FractionPoint := ⟨367887499047,483892000000,13279497179665187,17172649631200000⟩
theorem rev159_s3_ul_mem : rev159_s3_ul.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane79 rev159_vertex3 rev159_vertex2 rev159_s3_ul
    rev159_vertex3_mem rev159_vertex2_mem (by decide)
def rev159_s3_ur : FractionPoint := ⟨2017556719765051,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev159_s3_ur_mem : rev159_s3_ur.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane79 rev159_vertex3 rev159_vertex2 rev159_s3_ur
    rev159_vertex3_mem rev159_vertex2_mem (by decide)
theorem rev159_slab3 (p : Point) (hp : p∈IntegerCarrier rev159_planes)
    (hx0 : rev159_s3_ll.real.1≤p.1) (hx1 : p.1≤rev159_s3_lr.real.1) :
    p∈rationalHull (fractionRow159.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev159_plane32 rev159_plane79 rev159_s3_ll rev159_s3_lr rev159_s3_ul rev159_s3_ur
    (by decide) rev159_s3_ll_mem rev159_s3_lr_mem rev159_s3_ul_mem rev159_s3_ur_mem p
    (hp _ rev159_plane32_mem) (hp _ rev159_plane79_mem) hx0 hx1
def rev159_s4_ll : FractionPoint := ⟨2017556719765051,2631538706000000,45487520700431201821,59178042420528000000⟩
theorem rev159_s4_ll_mem : rev159_s4_ll.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane32 rev159_vertex0 rev159_vertex1 rev159_s4_ll
    rev159_vertex0_mem rev159_vertex1_mem (by decide)
def rev159_s4_lr : FractionPoint := ⟨1001990771613779,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev159_s4_lr_mem : rev159_s4_lr.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane32 rev159_vertex0 rev159_vertex1 rev159_s4_lr
    rev159_vertex0_mem rev159_vertex1_mem (by decide)
def rev159_s4_ul : FractionPoint := ⟨2017556719765051,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev159_s4_ul_mem : rev159_s4_ul.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane36 rev159_vertex2 rev159_vertex1 rev159_s4_ul
    rev159_vertex2_mem rev159_vertex1_mem (by decide)
def rev159_s4_ur : FractionPoint := ⟨1001990771613779,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev159_s4_ur_mem : rev159_s4_ur.real ∈ rationalHull (fractionRow159.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow159 rev159_plane36 rev159_vertex2 rev159_vertex1 rev159_s4_ur
    rev159_vertex2_mem rev159_vertex1_mem (by decide)
theorem rev159_slab4 (p : Point) (hp : p∈IntegerCarrier rev159_planes)
    (hx0 : rev159_s4_ll.real.1≤p.1) (hx1 : p.1≤rev159_s4_lr.real.1) :
    p∈rationalHull (fractionRow159.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev159_plane32 rev159_plane36 rev159_s4_ll rev159_s4_lr rev159_s4_ul rev159_s4_ur
    (by decide) rev159_s4_ll_mem rev159_s4_lr_mem rev159_s4_ul_mem rev159_s4_ur_mem p
    (hp _ rev159_plane32_mem) (hp _ rev159_plane36_mem) hx0 hx1
theorem rev159_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev159_planes) : rev159_s0_ll.real.1≤p.1 := by
  have hc := rev159_plane53.combine_sound rev159_plane75 2144520000000 2044968000000 (by decide) (by decide) p
    (hp _ rev159_plane53_mem) (hp _ rev159_plane75_mem)
  exact (rev159_plane53.combine rev159_plane75 2144520000000 2044968000000).xBoundCheck_sound rev159_s0_ll.nx rev159_s0_ll.dx true (by decide) p hc
theorem rev159_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev159_planes) : p.1≤rev159_s4_lr.real.1 := by
  have hc := rev159_plane32.combine_sound rev159_plane36 287616000000 1574160000000 (by decide) (by decide) p
    (hp _ rev159_plane32_mem) (hp _ rev159_plane36_mem)
  exact (rev159_plane32.combine rev159_plane36 287616000000 1574160000000).xBoundCheck_sound rev159_s4_lr.nx rev159_s4_lr.dx false (by decide) p hc
theorem rev159_hull (p : Point) (hp : p∈IntegerCarrier rev159_planes) :
    p∈rationalHull (fractionRow159.map FractionPoint.rational) := by
  have hxlo := rev159_bound0_lo p hp
  have hxhi := rev159_bound0_hi p hp
  by_cases h0 : p.1≤rev159_s0_lr.real.1
  · exact rev159_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev159_s1_lr.real.1
  · exact rev159_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev159_s2_lr.real.1
  · exact rev159_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev159_s3_lr.real.1
  · exact rev159_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev159_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull159 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,13,8,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow159 := by
  rw [← fractionRow159_correct]
  exact rev159_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull159
