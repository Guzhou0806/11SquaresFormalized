import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks5
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev45_planes : List IntegerPlane := integerOverlayPlanes ![4,7,2,5]
def rev45_plane4 : IntegerPlane := ⟨15204000000,(-2139684000000),(-568962228432)⟩
theorem rev45_plane4_mem : rev45_plane4 ∈ rev45_planes := by decide
def rev45_plane9 : IntegerPlane := ⟨2144520000000,(-699568000000),259009891352⟩
theorem rev45_plane9_mem : rev45_plane9 ∈ rev45_planes := by decide
def rev45_plane30 : IntegerPlane := ⟨2044968000000,643972000000,726507475981⟩
theorem rev45_plane30_mem : rev45_plane30 ∈ rev45_planes := by decide
def rev45_plane35 : IntegerPlane := ⟨(-48252000000),2112760000000,982750749085⟩
theorem rev45_plane35_mem : rev45_plane35 ∈ rev45_planes := by decide
def rev45_plane64 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-827972119784)⟩
theorem rev45_plane64_mem : rev45_plane64 ∈ rev45_planes := by decide
def rev45_plane65 : IntegerPlane := ⟨(-2139440000000),16372000000,(-377332847425)⟩
theorem rev45_plane65_mem : rev45_plane65 ∈ rev45_planes := by decide
def rev45_vertex0 : FractionPoint := fractionRow45[0]!
theorem rev45_vertex0_mem : rev45_vertex0∈fractionRow45 := by decide
def rev45_vertex1 : FractionPoint := fractionRow45[1]!
theorem rev45_vertex1_mem : rev45_vertex1∈fractionRow45 := by decide
def rev45_vertex2 : FractionPoint := fractionRow45[2]!
theorem rev45_vertex2_mem : rev45_vertex2∈fractionRow45 := by decide
def rev45_vertex3 : FractionPoint := fractionRow45[3]!
theorem rev45_vertex3_mem : rev45_vertex3∈fractionRow45 := by decide
def rev45_vertex4 : FractionPoint := fractionRow45[4]!
theorem rev45_vertex4_mem : rev45_vertex4∈fractionRow45 := by decide
def rev45_vertex5 : FractionPoint := fractionRow45[5]!
theorem rev45_vertex5_mem : rev45_vertex5∈fractionRow45 := by decide
def rev45_s0_ll : FractionPoint := ⟨204254107223178737,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev45_s0_ll_mem : rev45_s0_ll.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane64 rev45_vertex5 rev45_vertex0 rev45_s0_ll
    rev45_vertex5_mem rev45_vertex0_mem (by decide)
def rev45_s0_lr : FractionPoint := ⟨5834357507833289,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev45_s0_lr_mem : rev45_s0_lr.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane64 rev45_vertex5 rev45_vertex0 rev45_s0_lr
    rev45_vertex5_mem rev45_vertex0_mem (by decide)
def rev45_s0_ul : FractionPoint := ⟨204254107223178737,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev45_s0_ul_mem : rev45_s0_ul.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane65 rev45_vertex5 rev45_vertex4 rev45_s0_ul
    rev45_vertex5_mem rev45_vertex4_mem (by decide)
def rev45_s0_ur : FractionPoint := ⟨5834357507833289,32435075873000000,48687658190768828227,106205412438551200000⟩
theorem rev45_s0_ur_mem : rev45_s0_ur.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane65 rev45_vertex5 rev45_vertex4 rev45_s0_ur
    rev45_vertex5_mem rev45_vertex4_mem (by decide)
theorem rev45_slab0 (p : Point) (hp : p∈IntegerCarrier rev45_planes)
    (hx0 : rev45_s0_ll.real.1≤p.1) (hx1 : p.1≤rev45_s0_lr.real.1) :
    p∈rationalHull (fractionRow45.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev45_plane64 rev45_plane65 rev45_s0_ll rev45_s0_lr rev45_s0_ul rev45_s0_ur
    (by decide) rev45_s0_ll_mem rev45_s0_lr_mem rev45_s0_ul_mem rev45_s0_ur_mem p
    (hp _ rev45_plane64_mem) (hp _ rev45_plane65_mem) hx0 hx1
def rev45_s1_ll : FractionPoint := ⟨5834357507833289,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev45_s1_ll_mem : rev45_s1_ll.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane4 rev45_vertex0 rev45_vertex1 rev45_s1_ll
    rev45_vertex0_mem rev45_vertex1_mem (by decide)
def rev45_s1_lr : FractionPoint := ⟨40665167099483131,225966663632800000,53826987371851084204789,201457189461868348000000⟩
theorem rev45_s1_lr_mem : rev45_s1_lr.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane4 rev45_vertex0 rev45_vertex1 rev45_s1_lr
    rev45_vertex0_mem rev45_vertex1_mem (by decide)
def rev45_s1_ul : FractionPoint := ⟨5834357507833289,32435075873000000,48687658190768828227,106205412438551200000⟩
theorem rev45_s1_ul_mem : rev45_s1_ul.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane65 rev45_vertex5 rev45_vertex4 rev45_s1_ul
    rev45_vertex5_mem rev45_vertex4_mem (by decide)
def rev45_s1_ur : FractionPoint := ⟨40665167099483131,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev45_s1_ur_mem : rev45_s1_ur.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane65 rev45_vertex5 rev45_vertex4 rev45_s1_ur
    rev45_vertex5_mem rev45_vertex4_mem (by decide)
theorem rev45_slab1 (p : Point) (hp : p∈IntegerCarrier rev45_planes)
    (hx0 : rev45_s1_ll.real.1≤p.1) (hx1 : p.1≤rev45_s1_lr.real.1) :
    p∈rationalHull (fractionRow45.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev45_plane4 rev45_plane65 rev45_s1_ll rev45_s1_lr rev45_s1_ul rev45_s1_ur
    (by decide) rev45_s1_ll_mem rev45_s1_lr_mem rev45_s1_ul_mem rev45_s1_ur_mem p
    (hp _ rev45_plane4_mem) (hp _ rev45_plane65_mem) hx0 hx1
def rev45_s2_ll : FractionPoint := ⟨40665167099483131,225966663632800000,53826987371851084204789,201457189461868348000000⟩
theorem rev45_s2_ll_mem : rev45_s2_ll.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane4 rev45_vertex0 rev45_vertex1 rev45_s2_ll
    rev45_vertex0_mem rev45_vertex1_mem (by decide)
def rev45_s2_lr : FractionPoint := ⟨15034532826064199,72526658810400000,17288964356075004274537,64660054762529964000000⟩
theorem rev45_s2_lr_mem : rev45_s2_lr.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane4 rev45_vertex0 rev45_vertex1 rev45_s2_lr
    rev45_vertex0_mem rev45_vertex1_mem (by decide)
def rev45_s2_ul : FractionPoint := ⟨40665167099483131,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev45_s2_ul_mem : rev45_s2_ul.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane35 rev45_vertex4 rev45_vertex3 rev45_s2_ul
    rev45_vertex4_mem rev45_vertex3_mem (by decide)
def rev45_s2_ur : FractionPoint := ⟨15034532826064199,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev45_s2_ur_mem : rev45_s2_ur.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane35 rev45_vertex4 rev45_vertex3 rev45_s2_ur
    rev45_vertex4_mem rev45_vertex3_mem (by decide)
theorem rev45_slab2 (p : Point) (hp : p∈IntegerCarrier rev45_planes)
    (hx0 : rev45_s2_ll.real.1≤p.1) (hx1 : p.1≤rev45_s2_lr.real.1) :
    p∈rationalHull (fractionRow45.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev45_plane4 rev45_plane35 rev45_s2_ll rev45_s2_lr rev45_s2_ul rev45_s2_ur
    (by decide) rev45_s2_ll_mem rev45_s2_lr_mem rev45_s2_ul_mem rev45_s2_ur_mem p
    (hp _ rev45_plane4_mem) (hp _ rev45_plane35_mem) hx0 hx1
def rev45_s3_ll : FractionPoint := ⟨15034532826064199,72526658810400000,17288964356075004274537,64660054762529964000000⟩
theorem rev45_s3_ll_mem : rev45_s3_ll.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane4 rev45_vertex0 rev45_vertex1 rev45_s3_ll
    rev45_vertex0_mem rev45_vertex1_mem (by decide)
def rev45_s3_lr : FractionPoint := ⟨431262268381943,2073350951000000,79198296098933,296192993000000⟩
theorem rev45_s3_lr_mem : rev45_s3_lr.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane4 rev45_vertex0 rev45_vertex1 rev45_s3_lr
    rev45_vertex0_mem rev45_vertex1_mem (by decide)
def rev45_s3_ul : FractionPoint := ⟨15034532826064199,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev45_s3_ul_mem : rev45_s3_ul.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane30 rev45_vertex3 rev45_vertex2 rev45_s3_ul
    rev45_vertex3_mem rev45_vertex2_mem (by decide)
def rev45_s3_ur : FractionPoint := ⟨431262268381943,2073350951000000,624387427785330795107,1335179958617372000000⟩
theorem rev45_s3_ur_mem : rev45_s3_ur.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane30 rev45_vertex3 rev45_vertex2 rev45_s3_ur
    rev45_vertex3_mem rev45_vertex2_mem (by decide)
theorem rev45_slab3 (p : Point) (hp : p∈IntegerCarrier rev45_planes)
    (hx0 : rev45_s3_ll.real.1≤p.1) (hx1 : p.1≤rev45_s3_lr.real.1) :
    p∈rationalHull (fractionRow45.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev45_plane4 rev45_plane30 rev45_s3_ll rev45_s3_lr rev45_s3_ul rev45_s3_ur
    (by decide) rev45_s3_ll_mem rev45_s3_lr_mem rev45_s3_ul_mem rev45_s3_ur_mem p
    (hp _ rev45_plane4_mem) (hp _ rev45_plane30_mem) hx0 hx1
def rev45_s4_ll : FractionPoint := ⟨431262268381943,2073350951000000,79198296098933,296192993000000⟩
theorem rev45_s4_ll_mem : rev45_s4_ll.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane9 rev45_vertex1 rev45_vertex2 rev45_s4_ll
    rev45_vertex1_mem rev45_vertex2_mem (by decide)
def rev45_s4_lr : FractionPoint := ⟨611446104810513,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev45_s4_lr_mem : rev45_s4_lr.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane9 rev45_vertex1 rev45_vertex2 rev45_s4_lr
    rev45_vertex1_mem rev45_vertex2_mem (by decide)
def rev45_s4_ul : FractionPoint := ⟨431262268381943,2073350951000000,624387427785330795107,1335179958617372000000⟩
theorem rev45_s4_ul_mem : rev45_s4_ul.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane30 rev45_vertex3 rev45_vertex2 rev45_s4_ul
    rev45_vertex3_mem rev45_vertex2_mem (by decide)
def rev45_s4_ur : FractionPoint := ⟨611446104810513,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev45_s4_ur_mem : rev45_s4_ur.real ∈ rationalHull (fractionRow45.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow45 rev45_plane30 rev45_vertex3 rev45_vertex2 rev45_s4_ur
    rev45_vertex3_mem rev45_vertex2_mem (by decide)
theorem rev45_slab4 (p : Point) (hp : p∈IntegerCarrier rev45_planes)
    (hx0 : rev45_s4_ll.real.1≤p.1) (hx1 : p.1≤rev45_s4_lr.real.1) :
    p∈rationalHull (fractionRow45.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev45_plane9 rev45_plane30 rev45_s4_ll rev45_s4_lr rev45_s4_ul rev45_s4_ur
    (by decide) rev45_s4_ll_mem rev45_s4_lr_mem rev45_s4_ul_mem rev45_s4_ur_mem p
    (hp _ rev45_plane9_mem) (hp _ rev45_plane30_mem) hx0 hx1
theorem rev45_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev45_planes) : rev45_s0_ll.real.1≤p.1 := by
  have hc := rev45_plane64.combine_sound rev45_plane65 16372000000 2129316000000 (by decide) (by decide) p
    (hp _ rev45_plane64_mem) (hp _ rev45_plane65_mem)
  exact (rev45_plane64.combine rev45_plane65 16372000000 2129316000000).xBoundCheck_sound rev45_s0_ll.nx rev45_s0_ll.dx true (by decide) p hc
theorem rev45_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev45_planes) : p.1≤rev45_s4_lr.real.1 := by
  have hc := rev45_plane9.combine_sound rev45_plane30 643972000000 699568000000 (by decide) (by decide) p
    (hp _ rev45_plane9_mem) (hp _ rev45_plane30_mem)
  exact (rev45_plane9.combine rev45_plane30 643972000000 699568000000).xBoundCheck_sound rev45_s4_lr.nx rev45_s4_lr.dx false (by decide) p hc
theorem rev45_hull (p : Point) (hp : p∈IntegerCarrier rev45_planes) :
    p∈rationalHull (fractionRow45.map FractionPoint.rational) := by
  have hxlo := rev45_bound0_lo p hp
  have hxhi := rev45_bound0_hi p hp
  by_cases h0 : p.1≤rev45_s0_lr.real.1
  · exact rev45_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev45_s1_lr.real.1
  · exact rev45_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev45_s2_lr.real.1
  · exact rev45_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev45_s3_lr.real.1
  · exact rev45_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev45_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull45 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,7,2,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow45 := by
  rw [← fractionRow45_correct]
  exact rev45_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull45
