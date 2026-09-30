import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks3
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev31_planes : List IntegerPlane := integerOverlayPlanes ![2,5,11,8]
def rev31_plane24 : IntegerPlane := ⟨2129316000000,(-1440116000000),1301343880216⟩
theorem rev31_plane24_mem : rev31_plane24 ∈ rev31_planes := by decide
def rev31_plane25 : IntegerPlane := ⟨(-16372000000),(-2139440000000),(-393704847425)⟩
theorem rev31_plane25_mem : rev31_plane25 ∈ rev31_planes := by decide
def rev31_plane54 : IntegerPlane := ⟨699568000000,2144520000000,958577891352⟩
theorem rev31_plane54_mem : rev31_plane54 ∈ rev31_planes := by decide
def rev31_plane59 : IntegerPlane := ⟨2139684000000,15204000000,1570721771568⟩
theorem rev31_plane59_mem : rev31_plane59 ∈ rev31_planes := by decide
def rev31_plane68 : IntegerPlane := ⟨(-2112760000000),(-48252000000),(-1130009250915)⟩
theorem rev31_plane68_mem : rev31_plane68 ∈ rev31_planes := by decide
def rev31_plane73 : IntegerPlane := ⟨(-643972000000),2044968000000,82535475981⟩
theorem rev31_plane73_mem : rev31_plane73 ∈ rev31_planes := by decide
def rev31_vertex0 : FractionPoint := fractionRow31[0]!
theorem rev31_vertex0_mem : rev31_vertex0∈fractionRow31 := by decide
def rev31_vertex1 : FractionPoint := fractionRow31[1]!
theorem rev31_vertex1_mem : rev31_vertex1∈fractionRow31 := by decide
def rev31_vertex2 : FractionPoint := fractionRow31[2]!
theorem rev31_vertex2_mem : rev31_vertex2∈fractionRow31 := by decide
def rev31_vertex3 : FractionPoint := fractionRow31[3]!
theorem rev31_vertex3_mem : rev31_vertex3∈fractionRow31 := by decide
def rev31_vertex4 : FractionPoint := fractionRow31[4]!
theorem rev31_vertex4_mem : rev31_vertex4∈fractionRow31 := by decide
def rev31_vertex5 : FractionPoint := fractionRow31[5]!
theorem rev31_vertex5_mem : rev31_vertex5∈fractionRow31 := by decide
def rev31_s0_ll : FractionPoint := ⟨64079173778836403,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev31_s0_ll_mem : rev31_s0_ll.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane68 rev31_vertex5 rev31_vertex0 rev31_s0_ll
    rev31_vertex5_mem rev31_vertex0_mem (by decide)
def rev31_s0_lr : FractionPoint := ⟨4797179890959273,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev31_s0_lr_mem : rev31_s0_lr.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane68 rev31_vertex5 rev31_vertex0 rev31_s0_lr
    rev31_vertex5_mem rev31_vertex0_mem (by decide)
def rev31_s0_ul : FractionPoint := ⟨64079173778836403,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev31_s0_ul_mem : rev31_s0_ul.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane73 rev31_vertex5 rev31_vertex4 rev31_s0_ul
    rev31_vertex5_mem rev31_vertex4_mem (by decide)
def rev31_s0_ur : FractionPoint := ⟨4797179890959273,9038666545312000,19975313407769228002641,96269707540799948000000⟩
theorem rev31_s0_ur_mem : rev31_s0_ur.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane73 rev31_vertex5 rev31_vertex4 rev31_s0_ur
    rev31_vertex5_mem rev31_vertex4_mem (by decide)
theorem rev31_slab0 (p : Point) (hp : p∈IntegerCarrier rev31_planes)
    (hx0 : rev31_s0_ll.real.1≤p.1) (hx1 : p.1≤rev31_s0_lr.real.1) :
    p∈rationalHull (fractionRow31.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev31_plane68 rev31_plane73 rev31_s0_ll rev31_s0_lr rev31_s0_ul rev31_s0_ur
    (by decide) rev31_s0_ll_mem rev31_s0_lr_mem rev31_s0_ul_mem rev31_s0_ur_mem p
    (hp _ rev31_plane68_mem) (hp _ rev31_plane73_mem) hx0 hx1
def rev31_s1_ll : FractionPoint := ⟨4797179890959273,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev31_s1_ll_mem : rev31_s1_ll.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane25 rev31_vertex0 rev31_vertex1 rev31_s1_ll
    rev31_vertex0_mem rev31_vertex1_mem (by decide)
def rev31_s1_lr : FractionPoint := ⟨3230547344875983,5093487332000000,244055016471990090803,1362151317196760000000⟩
theorem rev31_s1_lr_mem : rev31_s1_lr.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane25 rev31_vertex0 rev31_vertex1 rev31_s1_lr
    rev31_vertex0_mem rev31_vertex1_mem (by decide)
def rev31_s1_ul : FractionPoint := ⟨4797179890959273,9038666545312000,19975313407769228002641,96269707540799948000000⟩
theorem rev31_s1_ul_mem : rev31_s1_ul.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane73 rev31_vertex5 rev31_vertex4 rev31_s1_ul
    rev31_vertex5_mem rev31_vertex4_mem (by decide)
def rev31_s1_ur : FractionPoint := ⟨3230547344875983,5093487332000000,611446104810513,2546743666000000⟩
theorem rev31_s1_ur_mem : rev31_s1_ur.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane73 rev31_vertex5 rev31_vertex4 rev31_s1_ur
    rev31_vertex5_mem rev31_vertex4_mem (by decide)
theorem rev31_slab1 (p : Point) (hp : p∈IntegerCarrier rev31_planes)
    (hx0 : rev31_s1_ll.real.1≤p.1) (hx1 : p.1≤rev31_s1_lr.real.1) :
    p∈rationalHull (fractionRow31.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev31_plane25 rev31_plane73 rev31_s1_ll rev31_s1_lr rev31_s1_ul rev31_s1_ur
    (by decide) rev31_s1_ll_mem rev31_s1_lr_mem rev31_s1_ul_mem rev31_s1_ur_mem p
    (hp _ rev31_plane25_mem) (hp _ rev31_plane73_mem) hx0 hx1
def rev31_s2_ll : FractionPoint := ⟨3230547344875983,5093487332000000,244055016471990090803,1362151317196760000000⟩
theorem rev31_s2_ll_mem : rev31_s2_ll.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane25 rev31_vertex0 rev31_vertex1 rev31_s2_ll
    rev31_vertex0_mem rev31_vertex1_mem (by decide)
def rev31_s2_lr : FractionPoint := ⟨167556390057181017,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev31_s2_lr_mem : rev31_s2_lr.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane25 rev31_vertex0 rev31_vertex1 rev31_s2_lr
    rev31_vertex0_mem rev31_vertex1_mem (by decide)
def rev31_s2_ul : FractionPoint := ⟨3230547344875983,5093487332000000,611446104810513,2546743666000000⟩
theorem rev31_s2_ul_mem : rev31_s2_ul.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane54 rev31_vertex4 rev31_vertex3 rev31_s2_ul
    rev31_vertex4_mem rev31_vertex3_mem (by decide)
def rev31_s2_ur : FractionPoint := ⟨167556390057181017,228956070109600000,463112039032513740179,2223735830939490000000⟩
theorem rev31_s2_ur_mem : rev31_s2_ur.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane54 rev31_vertex4 rev31_vertex3 rev31_s2_ur
    rev31_vertex4_mem rev31_vertex3_mem (by decide)
theorem rev31_slab2 (p : Point) (hp : p∈IntegerCarrier rev31_planes)
    (hx0 : rev31_s2_ll.real.1≤p.1) (hx1 : p.1≤rev31_s2_lr.real.1) :
    p∈rationalHull (fractionRow31.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev31_plane25 rev31_plane54 rev31_s2_ll rev31_s2_lr rev31_s2_ul rev31_s2_ur
    (by decide) rev31_s2_ll_mem rev31_s2_lr_mem rev31_s2_ul_mem rev31_s2_ur_mem p
    (hp _ rev31_plane25_mem) (hp _ rev31_plane54_mem) hx0 hx1
def rev31_s3_ll : FractionPoint := ⟨167556390057181017,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev31_s3_ll_mem : rev31_s3_ll.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane24 rev31_vertex1 rev31_vertex2 rev31_s3_ll
    rev31_vertex1_mem rev31_vertex2_mem (by decide)
def rev31_s3_lr : FractionPoint := ⟨216994696901067,296192993000000,19150335305795463421,106638067076797000000⟩
theorem rev31_s3_lr_mem : rev31_s3_lr.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane24 rev31_vertex1 rev31_vertex2 rev31_s3_lr
    rev31_vertex1_mem rev31_vertex2_mem (by decide)
def rev31_s3_ul : FractionPoint := ⟨167556390057181017,228956070109600000,463112039032513740179,2223735830939490000000⟩
theorem rev31_s3_ul_mem : rev31_s3_ul.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane54 rev31_vertex4 rev31_vertex3 rev31_s3_ul
    rev31_vertex4_mem rev31_vertex3_mem (by decide)
def rev31_s3_ur : FractionPoint := ⟨216994696901067,296192993000000,431262268381943,2073350951000000⟩
theorem rev31_s3_ur_mem : rev31_s3_ur.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane54 rev31_vertex4 rev31_vertex3 rev31_s3_ur
    rev31_vertex4_mem rev31_vertex3_mem (by decide)
theorem rev31_slab3 (p : Point) (hp : p∈IntegerCarrier rev31_planes)
    (hx0 : rev31_s3_ll.real.1≤p.1) (hx1 : p.1≤rev31_s3_lr.real.1) :
    p∈rationalHull (fractionRow31.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev31_plane24 rev31_plane54 rev31_s3_ll rev31_s3_lr rev31_s3_ul rev31_s3_ur
    (by decide) rev31_s3_ll_mem rev31_s3_lr_mem rev31_s3_ul_mem rev31_s3_ur_mem p
    (hp _ rev31_plane24_mem) (hp _ rev31_plane54_mem) hx0 hx1
def rev31_s4_ll : FractionPoint := ⟨216994696901067,296192993000000,19150335305795463421,106638067076797000000⟩
theorem rev31_s4_ll_mem : rev31_s4_ll.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane24 rev31_vertex1 rev31_vertex2 rev31_s4_ll
    rev31_vertex1_mem rev31_vertex2_mem (by decide)
def rev31_s4_lr : FractionPoint := ⟨23768824866023187,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev31_s4_lr_mem : rev31_s4_lr.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane24 rev31_vertex1 rev31_vertex2 rev31_s4_lr
    rev31_vertex1_mem rev31_vertex2_mem (by decide)
def rev31_s4_ul : FractionPoint := ⟨216994696901067,296192993000000,431262268381943,2073350951000000⟩
theorem rev31_s4_ul_mem : rev31_s4_ul.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane59 rev31_vertex3 rev31_vertex2 rev31_s4_ul
    rev31_vertex3_mem rev31_vertex2_mem (by decide)
def rev31_s4_ur : FractionPoint := ⟨23768824866023187,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev31_s4_ur_mem : rev31_s4_ur.real ∈ rationalHull (fractionRow31.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow31 rev31_plane59 rev31_vertex3 rev31_vertex2 rev31_s4_ur
    rev31_vertex3_mem rev31_vertex2_mem (by decide)
theorem rev31_slab4 (p : Point) (hp : p∈IntegerCarrier rev31_planes)
    (hx0 : rev31_s4_ll.real.1≤p.1) (hx1 : p.1≤rev31_s4_lr.real.1) :
    p∈rationalHull (fractionRow31.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev31_plane24 rev31_plane59 rev31_s4_ll rev31_s4_lr rev31_s4_ul rev31_s4_ur
    (by decide) rev31_s4_ll_mem rev31_s4_lr_mem rev31_s4_ul_mem rev31_s4_ur_mem p
    (hp _ rev31_plane24_mem) (hp _ rev31_plane59_mem) hx0 hx1
theorem rev31_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev31_planes) : rev31_s0_ll.real.1≤p.1 := by
  have hc := rev31_plane68.combine_sound rev31_plane73 2044968000000 48252000000 (by decide) (by decide) p
    (hp _ rev31_plane68_mem) (hp _ rev31_plane73_mem)
  exact (rev31_plane68.combine rev31_plane73 2044968000000 48252000000).xBoundCheck_sound rev31_s0_ll.nx rev31_s0_ll.dx true (by decide) p hc
theorem rev31_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev31_planes) : p.1≤rev31_s4_lr.real.1 := by
  have hc := rev31_plane24.combine_sound rev31_plane59 15204000000 1440116000000 (by decide) (by decide) p
    (hp _ rev31_plane24_mem) (hp _ rev31_plane59_mem)
  exact (rev31_plane24.combine rev31_plane59 15204000000 1440116000000).xBoundCheck_sound rev31_s4_lr.nx rev31_s4_lr.dx false (by decide) p hc
theorem rev31_hull (p : Point) (hp : p∈IntegerCarrier rev31_planes) :
    p∈rationalHull (fractionRow31.map FractionPoint.rational) := by
  have hxlo := rev31_bound0_lo p hp
  have hxhi := rev31_bound0_hi p hp
  by_cases h0 : p.1≤rev31_s0_lr.real.1
  · exact rev31_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev31_s1_lr.real.1
  · exact rev31_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev31_s2_lr.real.1
  · exact rev31_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev31_s3_lr.real.1
  · exact rev31_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev31_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull31 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,5,11,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow31 := by
  rw [← fractionRow31_correct]
  exact rev31_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull31
