import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks7
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev59_planes : List IntegerPlane := integerOverlayPlanes ![5,2,7,4]
def rev59_plane4 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-827972119784)⟩
theorem rev59_plane4_mem : rev59_plane4 ∈ rev59_planes := by decide
def rev59_plane5 : IntegerPlane := ⟨16372000000,(-2139440000000),(-377332847425)⟩
theorem rev59_plane5_mem : rev59_plane5 ∈ rev59_planes := by decide
def rev59_plane50 : IntegerPlane := ⟨643972000000,2044968000000,726507475981⟩
theorem rev59_plane50_mem : rev59_plane50 ∈ rev59_planes := by decide
def rev59_plane55 : IntegerPlane := ⟨2112760000000,(-48252000000),982750749085⟩
theorem rev59_plane55_mem : rev59_plane55 ∈ rev59_planes := by decide
def rev59_plane64 : IntegerPlane := ⟨(-2139684000000),15204000000,(-568962228432)⟩
theorem rev59_plane64_mem : rev59_plane64 ∈ rev59_planes := by decide
def rev59_plane69 : IntegerPlane := ⟨(-699568000000),2144520000000,259009891352⟩
theorem rev59_plane69_mem : rev59_plane69 ∈ rev59_planes := by decide
def rev59_vertex0 : FractionPoint := fractionRow59[0]!
theorem rev59_vertex0_mem : rev59_vertex0∈fractionRow59 := by decide
def rev59_vertex1 : FractionPoint := fractionRow59[1]!
theorem rev59_vertex1_mem : rev59_vertex1∈fractionRow59 := by decide
def rev59_vertex2 : FractionPoint := fractionRow59[2]!
theorem rev59_vertex2_mem : rev59_vertex2∈fractionRow59 := by decide
def rev59_vertex3 : FractionPoint := fractionRow59[3]!
theorem rev59_vertex3_mem : rev59_vertex3∈fractionRow59 := by decide
def rev59_vertex4 : FractionPoint := fractionRow59[4]!
theorem rev59_vertex4_mem : rev59_vertex4∈fractionRow59 := by decide
def rev59_vertex5 : FractionPoint := fractionRow59[5]!
theorem rev59_vertex5_mem : rev59_vertex5∈fractionRow59 := by decide
def rev59_s0_ll : FractionPoint := ⟨8666251006976813,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev59_s0_ll_mem : rev59_s0_ll.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane4 rev59_vertex0 rev59_vertex1 rev59_s0_ll
    rev59_vertex0_mem rev59_vertex1_mem (by decide)
def rev59_s0_lr : FractionPoint := ⟨79198296098933,296192993000000,19150335305795463421,106638067076797000000⟩
theorem rev59_s0_lr_mem : rev59_s0_lr.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane4 rev59_vertex0 rev59_vertex1 rev59_s0_lr
    rev59_vertex0_mem rev59_vertex1_mem (by decide)
def rev59_s0_ul : FractionPoint := ⟨8666251006976813,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev59_s0_ul_mem : rev59_s0_ul.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane64 rev59_vertex0 rev59_vertex5 rev59_s0_ul
    rev59_vertex0_mem rev59_vertex5_mem (by decide)
def rev59_s0_ur : FractionPoint := ⟨79198296098933,296192993000000,431262268381943,2073350951000000⟩
theorem rev59_s0_ur_mem : rev59_s0_ur.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane64 rev59_vertex0 rev59_vertex5 rev59_s0_ur
    rev59_vertex0_mem rev59_vertex5_mem (by decide)
theorem rev59_slab0 (p : Point) (hp : p∈IntegerCarrier rev59_planes)
    (hx0 : rev59_s0_ll.real.1≤p.1) (hx1 : p.1≤rev59_s0_lr.real.1) :
    p∈rationalHull (fractionRow59.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev59_plane4 rev59_plane64 rev59_s0_ll rev59_s0_lr rev59_s0_ul rev59_s0_ur
    (by decide) rev59_s0_ll_mem rev59_s0_lr_mem rev59_s0_ul_mem rev59_s0_ur_mem p
    (hp _ rev59_plane4_mem) (hp _ rev59_plane64_mem) hx0 hx1
def rev59_s1_ll : FractionPoint := ⟨79198296098933,296192993000000,19150335305795463421,106638067076797000000⟩
theorem rev59_s1_ll_mem : rev59_s1_ll.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane4 rev59_vertex0 rev59_vertex1 rev59_s1_ll
    rev59_vertex0_mem rev59_vertex1_mem (by decide)
def rev59_s1_lr : FractionPoint := ⟨61399680052418983,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev59_s1_lr_mem : rev59_s1_lr.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane4 rev59_vertex0 rev59_vertex1 rev59_s1_lr
    rev59_vertex0_mem rev59_vertex1_mem (by decide)
def rev59_s1_ul : FractionPoint := ⟨79198296098933,296192993000000,431262268381943,2073350951000000⟩
theorem rev59_s1_ul_mem : rev59_s1_ul.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane69 rev59_vertex5 rev59_vertex4 rev59_s1_ul
    rev59_vertex5_mem rev59_vertex4_mem (by decide)
def rev59_s1_ur : FractionPoint := ⟨61399680052418983,228956070109600000,463112039032513740179,2223735830939490000000⟩
theorem rev59_s1_ur_mem : rev59_s1_ur.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane69 rev59_vertex5 rev59_vertex4 rev59_s1_ur
    rev59_vertex5_mem rev59_vertex4_mem (by decide)
theorem rev59_slab1 (p : Point) (hp : p∈IntegerCarrier rev59_planes)
    (hx0 : rev59_s1_ll.real.1≤p.1) (hx1 : p.1≤rev59_s1_lr.real.1) :
    p∈rationalHull (fractionRow59.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev59_plane4 rev59_plane69 rev59_s1_ll rev59_s1_lr rev59_s1_ul rev59_s1_ur
    (by decide) rev59_s1_ll_mem rev59_s1_lr_mem rev59_s1_ul_mem rev59_s1_ur_mem p
    (hp _ rev59_plane4_mem) (hp _ rev59_plane69_mem) hx0 hx1
def rev59_s2_ll : FractionPoint := ⟨61399680052418983,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev59_s2_ll_mem : rev59_s2_ll.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane5 rev59_vertex1 rev59_vertex2 rev59_s2_ll
    rev59_vertex1_mem rev59_vertex2_mem (by decide)
def rev59_s2_lr : FractionPoint := ⟨1862939987124017,5093487332000000,244055016471990090803,1362151317196760000000⟩
theorem rev59_s2_lr_mem : rev59_s2_lr.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane5 rev59_vertex1 rev59_vertex2 rev59_s2_lr
    rev59_vertex1_mem rev59_vertex2_mem (by decide)
def rev59_s2_ul : FractionPoint := ⟨61399680052418983,228956070109600000,463112039032513740179,2223735830939490000000⟩
theorem rev59_s2_ul_mem : rev59_s2_ul.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane69 rev59_vertex5 rev59_vertex4 rev59_s2_ul
    rev59_vertex5_mem rev59_vertex4_mem (by decide)
def rev59_s2_ur : FractionPoint := ⟨1862939987124017,5093487332000000,611446104810513,2546743666000000⟩
theorem rev59_s2_ur_mem : rev59_s2_ur.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane69 rev59_vertex5 rev59_vertex4 rev59_s2_ur
    rev59_vertex5_mem rev59_vertex4_mem (by decide)
theorem rev59_slab2 (p : Point) (hp : p∈IntegerCarrier rev59_planes)
    (hx0 : rev59_s2_ll.real.1≤p.1) (hx1 : p.1≤rev59_s2_lr.real.1) :
    p∈rationalHull (fractionRow59.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev59_plane5 rev59_plane69 rev59_s2_ll rev59_s2_lr rev59_s2_ul rev59_s2_ur
    (by decide) rev59_s2_ll_mem rev59_s2_lr_mem rev59_s2_ul_mem rev59_s2_ur_mem p
    (hp _ rev59_plane5_mem) (hp _ rev59_plane69_mem) hx0 hx1
def rev59_s3_ll : FractionPoint := ⟨1862939987124017,5093487332000000,244055016471990090803,1362151317196760000000⟩
theorem rev59_s3_ll_mem : rev59_s3_ll.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane5 rev59_vertex1 rev59_vertex2 rev59_s3_ll
    rev59_vertex1_mem rev59_vertex2_mem (by decide)
def rev59_s3_lr : FractionPoint := ⟨4241486654352727,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev59_s3_lr_mem : rev59_s3_lr.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane5 rev59_vertex1 rev59_vertex2 rev59_s3_lr
    rev59_vertex1_mem rev59_vertex2_mem (by decide)
def rev59_s3_ul : FractionPoint := ⟨1862939987124017,5093487332000000,611446104810513,2546743666000000⟩
theorem rev59_s3_ul_mem : rev59_s3_ul.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane50 rev59_vertex4 rev59_vertex3 rev59_s3_ul
    rev59_vertex4_mem rev59_vertex3_mem (by decide)
def rev59_s3_ur : FractionPoint := ⟨4241486654352727,9038666545312000,19975313407769228002641,96269707540799948000000⟩
theorem rev59_s3_ur_mem : rev59_s3_ur.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane50 rev59_vertex4 rev59_vertex3 rev59_s3_ur
    rev59_vertex4_mem rev59_vertex3_mem (by decide)
theorem rev59_slab3 (p : Point) (hp : p∈IntegerCarrier rev59_planes)
    (hx0 : rev59_s3_ll.real.1≤p.1) (hx1 : p.1≤rev59_s3_lr.real.1) :
    p∈rationalHull (fractionRow59.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev59_plane5 rev59_plane50 rev59_s3_ll rev59_s3_lr rev59_s3_ul rev59_s3_ur
    (by decide) rev59_s3_ll_mem rev59_s3_lr_mem rev59_s3_ul_mem rev59_s3_ur_mem p
    (hp _ rev59_plane5_mem) (hp _ rev59_plane50_mem) hx0 hx1
def rev59_s4_ll : FractionPoint := ⟨4241486654352727,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev59_s4_ll_mem : rev59_s4_ll.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane55 rev59_vertex2 rev59_vertex3 rev59_s4_ll
    rev59_vertex2_mem rev59_vertex3_mem (by decide)
def rev59_s4_lr : FractionPoint := ⟨56798590905163597,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev59_s4_lr_mem : rev59_s4_lr.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane55 rev59_vertex2 rev59_vertex3 rev59_s4_lr
    rev59_vertex2_mem rev59_vertex3_mem (by decide)
def rev59_s4_ul : FractionPoint := ⟨4241486654352727,9038666545312000,19975313407769228002641,96269707540799948000000⟩
theorem rev59_s4_ul_mem : rev59_s4_ul.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane50 rev59_vertex4 rev59_vertex3 rev59_s4_ul
    rev59_vertex4_mem rev59_vertex3_mem (by decide)
def rev59_s4_ur : FractionPoint := ⟨56798590905163597,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev59_s4_ur_mem : rev59_s4_ur.real ∈ rationalHull (fractionRow59.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow59 rev59_plane50 rev59_vertex4 rev59_vertex3 rev59_s4_ur
    rev59_vertex4_mem rev59_vertex3_mem (by decide)
theorem rev59_slab4 (p : Point) (hp : p∈IntegerCarrier rev59_planes)
    (hx0 : rev59_s4_ll.real.1≤p.1) (hx1 : p.1≤rev59_s4_lr.real.1) :
    p∈rationalHull (fractionRow59.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev59_plane55 rev59_plane50 rev59_s4_ll rev59_s4_lr rev59_s4_ul rev59_s4_ur
    (by decide) rev59_s4_ll_mem rev59_s4_lr_mem rev59_s4_ul_mem rev59_s4_ur_mem p
    (hp _ rev59_plane55_mem) (hp _ rev59_plane50_mem) hx0 hx1
theorem rev59_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev59_planes) : rev59_s0_ll.real.1≤p.1 := by
  have hc := rev59_plane4.combine_sound rev59_plane64 15204000000 1440116000000 (by decide) (by decide) p
    (hp _ rev59_plane4_mem) (hp _ rev59_plane64_mem)
  exact (rev59_plane4.combine rev59_plane64 15204000000 1440116000000).xBoundCheck_sound rev59_s0_ll.nx rev59_s0_ll.dx true (by decide) p hc
theorem rev59_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev59_planes) : p.1≤rev59_s4_lr.real.1 := by
  have hc := rev59_plane50.combine_sound rev59_plane55 48252000000 2044968000000 (by decide) (by decide) p
    (hp _ rev59_plane50_mem) (hp _ rev59_plane55_mem)
  exact (rev59_plane50.combine rev59_plane55 48252000000 2044968000000).xBoundCheck_sound rev59_s4_lr.nx rev59_s4_lr.dx false (by decide) p hc
theorem rev59_hull (p : Point) (hp : p∈IntegerCarrier rev59_planes) :
    p∈rationalHull (fractionRow59.map FractionPoint.rational) := by
  have hxlo := rev59_bound0_lo p hp
  have hxhi := rev59_bound0_hi p hp
  by_cases h0 : p.1≤rev59_s0_lr.real.1
  · exact rev59_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev59_s1_lr.real.1
  · exact rev59_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev59_s2_lr.real.1
  · exact rev59_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev59_s3_lr.real.1
  · exact rev59_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev59_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull59 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,2,7,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow59 := by
  rw [← fractionRow59_correct]
  exact rev59_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull59
