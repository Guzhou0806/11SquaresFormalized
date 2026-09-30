import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks12
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev101_planes : List IntegerPlane := integerOverlayPlanes ![7,4,10,13]
def rev101_plane10 : IntegerPlane := ⟨(-2044968000000),643972000000,(-1318460524019)⟩
theorem rev101_plane10_mem : rev101_plane10 ∈ rev101_planes := by decide
def rev101_plane15 : IntegerPlane := ⟨48252000000,2112760000000,1031002749085⟩
theorem rev101_plane15_mem : rev101_plane15 ∈ rev101_planes := by decide
def rev101_plane24 : IntegerPlane := ⟨(-15204000000),(-2139684000000),(-584166228432)⟩
theorem rev101_plane24_mem : rev101_plane24 ∈ rev101_planes := by decide
def rev101_plane29 : IntegerPlane := ⟨(-2144520000000),(-699568000000),(-1885510108648)⟩
theorem rev101_plane29_mem : rev101_plane29 ∈ rev101_planes := by decide
def rev101_plane58 : IntegerPlane := ⟨2139440000000,16372000000,1762107152575⟩
theorem rev101_plane58_mem : rev101_plane58 ∈ rev101_planes := by decide
def rev101_plane59 : IntegerPlane := ⟨1440116000000,(-2129316000000),612143880216⟩
theorem rev101_plane59_mem : rev101_plane59 ∈ rev101_planes := by decide
def rev101_vertex0 : FractionPoint := fractionRow101[0]!
theorem rev101_vertex0_mem : rev101_vertex0∈fractionRow101 := by decide
def rev101_vertex1 : FractionPoint := fractionRow101[1]!
theorem rev101_vertex1_mem : rev101_vertex1∈fractionRow101 := by decide
def rev101_vertex2 : FractionPoint := fractionRow101[2]!
theorem rev101_vertex2_mem : rev101_vertex2∈fractionRow101 := by decide
def rev101_vertex3 : FractionPoint := fractionRow101[3]!
theorem rev101_vertex3_mem : rev101_vertex3∈fractionRow101 := by decide
def rev101_vertex4 : FractionPoint := fractionRow101[4]!
theorem rev101_vertex4_mem : rev101_vertex4∈fractionRow101 := by decide
def rev101_vertex5 : FractionPoint := fractionRow101[5]!
theorem rev101_vertex5_mem : rev101_vertex5∈fractionRow101 := by decide
def rev101_s0_ll : FractionPoint := ⟨1935297561189487,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev101_s0_ll_mem : rev101_s0_ll.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane29 rev101_vertex2 rev101_vertex3 rev101_s0_ll
    rev101_vertex2_mem rev101_vertex3_mem (by decide)
def rev101_s0_lr : FractionPoint := ⟨1642088682618057,2073350951000000,79198296098933,296192993000000⟩
theorem rev101_s0_lr_mem : rev101_s0_lr.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane29 rev101_vertex2 rev101_vertex3 rev101_s0_lr
    rev101_vertex2_mem rev101_vertex3_mem (by decide)
def rev101_s0_ul : FractionPoint := ⟨1935297561189487,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev101_s0_ul_mem : rev101_s0_ul.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane10 rev101_vertex2 rev101_vertex1 rev101_s0_ul
    rev101_vertex2_mem rev101_vertex1_mem (by decide)
def rev101_s0_ur : FractionPoint := ⟨1642088682618057,2073350951000000,624387427785330795107,1335179958617372000000⟩
theorem rev101_s0_ur_mem : rev101_s0_ur.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane10 rev101_vertex2 rev101_vertex1 rev101_s0_ur
    rev101_vertex2_mem rev101_vertex1_mem (by decide)
theorem rev101_slab0 (p : Point) (hp : p∈IntegerCarrier rev101_planes)
    (hx0 : rev101_s0_ll.real.1≤p.1) (hx1 : p.1≤rev101_s0_lr.real.1) :
    p∈rationalHull (fractionRow101.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev101_plane29 rev101_plane10 rev101_s0_ll rev101_s0_lr rev101_s0_ul rev101_s0_ur
    (by decide) rev101_s0_ll_mem rev101_s0_lr_mem rev101_s0_ul_mem rev101_s0_ur_mem p
    (hp _ rev101_plane29_mem) (hp _ rev101_plane10_mem) hx0 hx1
def rev101_s1_ll : FractionPoint := ⟨1642088682618057,2073350951000000,79198296098933,296192993000000⟩
theorem rev101_s1_ll_mem : rev101_s1_ll.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane24 rev101_vertex3 rev101_vertex4 rev101_s1_ll
    rev101_vertex3_mem rev101_vertex4_mem (by decide)
def rev101_s1_lr : FractionPoint := ⟨57492125984335801,72526658810400000,17288964356075004274537,64660054762529964000000⟩
theorem rev101_s1_lr_mem : rev101_s1_lr.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane24 rev101_vertex3 rev101_vertex4 rev101_s1_lr
    rev101_vertex3_mem rev101_vertex4_mem (by decide)
def rev101_s1_ul : FractionPoint := ⟨1642088682618057,2073350951000000,624387427785330795107,1335179958617372000000⟩
theorem rev101_s1_ul_mem : rev101_s1_ul.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane10 rev101_vertex2 rev101_vertex1 rev101_s1_ul
    rev101_vertex2_mem rev101_vertex1_mem (by decide)
def rev101_s1_ur : FractionPoint := ⟨57492125984335801,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev101_s1_ur_mem : rev101_s1_ur.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane10 rev101_vertex2 rev101_vertex1 rev101_s1_ur
    rev101_vertex2_mem rev101_vertex1_mem (by decide)
theorem rev101_slab1 (p : Point) (hp : p∈IntegerCarrier rev101_planes)
    (hx0 : rev101_s1_ll.real.1≤p.1) (hx1 : p.1≤rev101_s1_lr.real.1) :
    p∈rationalHull (fractionRow101.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev101_plane24 rev101_plane10 rev101_s1_ll rev101_s1_lr rev101_s1_ul rev101_s1_ur
    (by decide) rev101_s1_ll_mem rev101_s1_lr_mem rev101_s1_ul_mem rev101_s1_ur_mem p
    (hp _ rev101_plane24_mem) (hp _ rev101_plane10_mem) hx0 hx1
def rev101_s2_ll : FractionPoint := ⟨57492125984335801,72526658810400000,17288964356075004274537,64660054762529964000000⟩
theorem rev101_s2_ll_mem : rev101_s2_ll.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane24 rev101_vertex3 rev101_vertex4 rev101_s2_ll
    rev101_vertex3_mem rev101_vertex4_mem (by decide)
def rev101_s2_lr : FractionPoint := ⟨185301496533316869,225966663632800000,53826987371851084204789,201457189461868348000000⟩
theorem rev101_s2_lr_mem : rev101_s2_lr.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane24 rev101_vertex3 rev101_vertex4 rev101_s2_lr
    rev101_vertex3_mem rev101_vertex4_mem (by decide)
def rev101_s2_ul : FractionPoint := ⟨57492125984335801,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev101_s2_ul_mem : rev101_s2_ul.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane15 rev101_vertex1 rev101_vertex0 rev101_s2_ul
    rev101_vertex1_mem rev101_vertex0_mem (by decide)
def rev101_s2_ur : FractionPoint := ⟨185301496533316869,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev101_s2_ur_mem : rev101_s2_ur.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane15 rev101_vertex1 rev101_vertex0 rev101_s2_ur
    rev101_vertex1_mem rev101_vertex0_mem (by decide)
theorem rev101_slab2 (p : Point) (hp : p∈IntegerCarrier rev101_planes)
    (hx0 : rev101_s2_ll.real.1≤p.1) (hx1 : p.1≤rev101_s2_lr.real.1) :
    p∈rationalHull (fractionRow101.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev101_plane24 rev101_plane15 rev101_s2_ll rev101_s2_lr rev101_s2_ul rev101_s2_ur
    (by decide) rev101_s2_ll_mem rev101_s2_lr_mem rev101_s2_ul_mem rev101_s2_ur_mem p
    (hp _ rev101_plane24_mem) (hp _ rev101_plane15_mem) hx0 hx1
def rev101_s3_ll : FractionPoint := ⟨185301496533316869,225966663632800000,53826987371851084204789,201457189461868348000000⟩
theorem rev101_s3_ll_mem : rev101_s3_ll.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane24 rev101_vertex3 rev101_vertex4 rev101_s3_ll
    rev101_vertex3_mem rev101_vertex4_mem (by decide)
def rev101_s3_lr : FractionPoint := ⟨26600718365166711,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev101_s3_lr_mem : rev101_s3_lr.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane24 rev101_vertex3 rev101_vertex4 rev101_s3_lr
    rev101_vertex3_mem rev101_vertex4_mem (by decide)
def rev101_s3_ul : FractionPoint := ⟨185301496533316869,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev101_s3_ul_mem : rev101_s3_ul.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane58 rev101_vertex0 rev101_vertex5 rev101_s3_ul
    rev101_vertex0_mem rev101_vertex5_mem (by decide)
def rev101_s3_ur : FractionPoint := ⟨26600718365166711,32435075873000000,48687658190768828227,106205412438551200000⟩
theorem rev101_s3_ur_mem : rev101_s3_ur.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane58 rev101_vertex0 rev101_vertex5 rev101_s3_ur
    rev101_vertex0_mem rev101_vertex5_mem (by decide)
theorem rev101_slab3 (p : Point) (hp : p∈IntegerCarrier rev101_planes)
    (hx0 : rev101_s3_ll.real.1≤p.1) (hx1 : p.1≤rev101_s3_lr.real.1) :
    p∈rationalHull (fractionRow101.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev101_plane24 rev101_plane58 rev101_s3_ll rev101_s3_lr rev101_s3_ul rev101_s3_ur
    (by decide) rev101_s3_ll_mem rev101_s3_lr_mem rev101_s3_ul_mem rev101_s3_ur_mem p
    (hp _ rev101_plane24_mem) (hp _ rev101_plane58_mem) hx0 hx1
def rev101_s4_ll : FractionPoint := ⟨26600718365166711,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev101_s4_ll_mem : rev101_s4_ll.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane59 rev101_vertex4 rev101_vertex5 rev101_s4_ll
    rev101_vertex4_mem rev101_vertex5_mem (by decide)
def rev101_s4_lr : FractionPoint := ⟨940526243324821263,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev101_s4_lr_mem : rev101_s4_lr.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane59 rev101_vertex4 rev101_vertex5 rev101_s4_lr
    rev101_vertex4_mem rev101_vertex5_mem (by decide)
def rev101_s4_ul : FractionPoint := ⟨26600718365166711,32435075873000000,48687658190768828227,106205412438551200000⟩
theorem rev101_s4_ul_mem : rev101_s4_ul.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane58 rev101_vertex0 rev101_vertex5 rev101_s4_ul
    rev101_vertex0_mem rev101_vertex5_mem (by decide)
def rev101_s4_ur : FractionPoint := ⟨940526243324821263,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev101_s4_ur_mem : rev101_s4_ur.real ∈ rationalHull (fractionRow101.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow101 rev101_plane58 rev101_vertex0 rev101_vertex5 rev101_s4_ur
    rev101_vertex0_mem rev101_vertex5_mem (by decide)
theorem rev101_slab4 (p : Point) (hp : p∈IntegerCarrier rev101_planes)
    (hx0 : rev101_s4_ll.real.1≤p.1) (hx1 : p.1≤rev101_s4_lr.real.1) :
    p∈rationalHull (fractionRow101.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev101_plane59 rev101_plane58 rev101_s4_ll rev101_s4_lr rev101_s4_ul rev101_s4_ur
    (by decide) rev101_s4_ll_mem rev101_s4_lr_mem rev101_s4_ul_mem rev101_s4_ur_mem p
    (hp _ rev101_plane59_mem) (hp _ rev101_plane58_mem) hx0 hx1
theorem rev101_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev101_planes) : rev101_s0_ll.real.1≤p.1 := by
  have hc := rev101_plane10.combine_sound rev101_plane29 699568000000 643972000000 (by decide) (by decide) p
    (hp _ rev101_plane10_mem) (hp _ rev101_plane29_mem)
  exact (rev101_plane10.combine rev101_plane29 699568000000 643972000000).xBoundCheck_sound rev101_s0_ll.nx rev101_s0_ll.dx true (by decide) p hc
theorem rev101_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev101_planes) : p.1≤rev101_s4_lr.real.1 := by
  have hc := rev101_plane58.combine_sound rev101_plane59 2129316000000 16372000000 (by decide) (by decide) p
    (hp _ rev101_plane58_mem) (hp _ rev101_plane59_mem)
  exact (rev101_plane58.combine rev101_plane59 2129316000000 16372000000).xBoundCheck_sound rev101_s4_lr.nx rev101_s4_lr.dx false (by decide) p hc
theorem rev101_hull (p : Point) (hp : p∈IntegerCarrier rev101_planes) :
    p∈rationalHull (fractionRow101.map FractionPoint.rational) := by
  have hxlo := rev101_bound0_lo p hp
  have hxhi := rev101_bound0_hi p hp
  by_cases h0 : p.1≤rev101_s0_lr.real.1
  · exact rev101_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev101_s1_lr.real.1
  · exact rev101_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev101_s2_lr.real.1
  · exact rev101_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev101_s3_lr.real.1
  · exact rev101_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev101_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull101 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,4,10,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow101 := by
  rw [← fractionRow101_correct]
  exact rev101_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull101
