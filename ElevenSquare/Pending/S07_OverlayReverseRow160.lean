import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks20
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev160_planes : List IntegerPlane := integerOverlayPlanes ![10,13,8,11]
def rev160_plane18 : IntegerPlane := ⟨(-16372000000),2139440000000,1745735152575⟩
theorem rev160_plane18_mem : rev160_plane18 ∈ rev160_planes := by decide
def rev160_plane19 : IntegerPlane := ⟨2129316000000,1440116000000,2741459880216⟩
theorem rev160_plane19_mem : rev160_plane19 ∈ rev160_planes := by decide
def rev160_plane48 : IntegerPlane := ⟨(-2112760000000),48252000000,(-1081757250915)⟩
theorem rev160_plane48_mem : rev160_plane48 ∈ rev160_planes := by decide
def rev160_plane53 : IntegerPlane := ⟨(-643972000000),(-2044968000000),(-1962432524019)⟩
theorem rev160_plane53_mem : rev160_plane53 ∈ rev160_planes := by decide
def rev160_plane74 : IntegerPlane := ⟨699568000000,(-2144520000000),(-1185942108648)⟩
theorem rev160_plane74_mem : rev160_plane74 ∈ rev160_planes := by decide
def rev160_plane79 : IntegerPlane := ⟨2139684000000,(-15204000000),1555517771568⟩
theorem rev160_plane79_mem : rev160_plane79 ∈ rev160_planes := by decide
def rev160_vertex0 : FractionPoint := fractionRow160[0]!
theorem rev160_vertex0_mem : rev160_vertex0∈fractionRow160 := by decide
def rev160_vertex1 : FractionPoint := fractionRow160[1]!
theorem rev160_vertex1_mem : rev160_vertex1∈fractionRow160 := by decide
def rev160_vertex2 : FractionPoint := fractionRow160[2]!
theorem rev160_vertex2_mem : rev160_vertex2∈fractionRow160 := by decide
def rev160_vertex3 : FractionPoint := fractionRow160[3]!
theorem rev160_vertex3_mem : rev160_vertex3∈fractionRow160 := by decide
def rev160_vertex4 : FractionPoint := fractionRow160[4]!
theorem rev160_vertex4_mem : rev160_vertex4∈fractionRow160 := by decide
def rev160_vertex5 : FractionPoint := fractionRow160[5]!
theorem rev160_vertex5_mem : rev160_vertex5∈fractionRow160 := by decide
def rev160_s0_ll : FractionPoint := ⟨64079173778836403,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev160_s0_ll_mem : rev160_s0_ll.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane53 rev160_vertex3 rev160_vertex4 rev160_s0_ll
    rev160_vertex3_mem rev160_vertex4_mem (by decide)
def rev160_s0_lr : FractionPoint := ⟨4797179890959273,9038666545312000,76294394133030719997359,96269707540799948000000⟩
theorem rev160_s0_lr_mem : rev160_s0_lr.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane53 rev160_vertex3 rev160_vertex4 rev160_s0_lr
    rev160_vertex3_mem rev160_vertex4_mem (by decide)
def rev160_s0_ul : FractionPoint := ⟨64079173778836403,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev160_s0_ul_mem : rev160_s0_ul.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane48 rev160_vertex3 rev160_vertex2 rev160_s0_ul
    rev160_vertex3_mem rev160_vertex2_mem (by decide)
def rev160_s0_ur : FractionPoint := ⟨4797179890959273,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev160_s0_ur_mem : rev160_s0_ur.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane48 rev160_vertex3 rev160_vertex2 rev160_s0_ur
    rev160_vertex3_mem rev160_vertex2_mem (by decide)
theorem rev160_slab0 (p : Point) (hp : p∈IntegerCarrier rev160_planes)
    (hx0 : rev160_s0_ll.real.1≤p.1) (hx1 : p.1≤rev160_s0_lr.real.1) :
    p∈rationalHull (fractionRow160.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev160_plane53 rev160_plane48 rev160_s0_ll rev160_s0_lr rev160_s0_ul rev160_s0_ur
    (by decide) rev160_s0_ll_mem rev160_s0_lr_mem rev160_s0_ul_mem rev160_s0_ur_mem p
    (hp _ rev160_plane53_mem) (hp _ rev160_plane48_mem) hx0 hx1
def rev160_s1_ll : FractionPoint := ⟨4797179890959273,9038666545312000,76294394133030719997359,96269707540799948000000⟩
theorem rev160_s1_ll_mem : rev160_s1_ll.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane53 rev160_vertex3 rev160_vertex4 rev160_s1_ll
    rev160_vertex3_mem rev160_vertex4_mem (by decide)
def rev160_s1_lr : FractionPoint := ⟨3230547344875983,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev160_s1_lr_mem : rev160_s1_lr.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane53 rev160_vertex3 rev160_vertex4 rev160_s1_lr
    rev160_vertex3_mem rev160_vertex4_mem (by decide)
def rev160_s1_ul : FractionPoint := ⟨4797179890959273,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev160_s1_ul_mem : rev160_s1_ul.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane18 rev160_vertex2 rev160_vertex1 rev160_s1_ul
    rev160_vertex2_mem rev160_vertex1_mem (by decide)
def rev160_s1_ur : FractionPoint := ⟨3230547344875983,5093487332000000,1118096300724769909197,1362151317196760000000⟩
theorem rev160_s1_ur_mem : rev160_s1_ur.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane18 rev160_vertex2 rev160_vertex1 rev160_s1_ur
    rev160_vertex2_mem rev160_vertex1_mem (by decide)
theorem rev160_slab1 (p : Point) (hp : p∈IntegerCarrier rev160_planes)
    (hx0 : rev160_s1_ll.real.1≤p.1) (hx1 : p.1≤rev160_s1_lr.real.1) :
    p∈rationalHull (fractionRow160.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev160_plane53 rev160_plane18 rev160_s1_ll rev160_s1_lr rev160_s1_ul rev160_s1_ur
    (by decide) rev160_s1_ll_mem rev160_s1_lr_mem rev160_s1_ul_mem rev160_s1_ur_mem p
    (hp _ rev160_plane53_mem) (hp _ rev160_plane18_mem) hx0 hx1
def rev160_s2_ll : FractionPoint := ⟨3230547344875983,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev160_s2_ll_mem : rev160_s2_ll.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane74 rev160_vertex4 rev160_vertex5 rev160_s2_ll
    rev160_vertex4_mem rev160_vertex5_mem (by decide)
def rev160_s2_lr : FractionPoint := ⟨167556390057181017,228956070109600000,1760623791906976259821,2223735830939490000000⟩
theorem rev160_s2_lr_mem : rev160_s2_lr.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane74 rev160_vertex4 rev160_vertex5 rev160_s2_lr
    rev160_vertex4_mem rev160_vertex5_mem (by decide)
def rev160_s2_ul : FractionPoint := ⟨3230547344875983,5093487332000000,1118096300724769909197,1362151317196760000000⟩
theorem rev160_s2_ul_mem : rev160_s2_ul.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane18 rev160_vertex2 rev160_vertex1 rev160_s2_ul
    rev160_vertex2_mem rev160_vertex1_mem (by decide)
def rev160_s2_ur : FractionPoint := ⟨167556390057181017,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev160_s2_ur_mem : rev160_s2_ur.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane18 rev160_vertex2 rev160_vertex1 rev160_s2_ur
    rev160_vertex2_mem rev160_vertex1_mem (by decide)
theorem rev160_slab2 (p : Point) (hp : p∈IntegerCarrier rev160_planes)
    (hx0 : rev160_s2_ll.real.1≤p.1) (hx1 : p.1≤rev160_s2_lr.real.1) :
    p∈rationalHull (fractionRow160.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev160_plane74 rev160_plane18 rev160_s2_ll rev160_s2_lr rev160_s2_ul rev160_s2_ur
    (by decide) rev160_s2_ll_mem rev160_s2_lr_mem rev160_s2_ul_mem rev160_s2_ur_mem p
    (hp _ rev160_plane74_mem) (hp _ rev160_plane18_mem) hx0 hx1
def rev160_s3_ll : FractionPoint := ⟨167556390057181017,228956070109600000,1760623791906976259821,2223735830939490000000⟩
theorem rev160_s3_ll_mem : rev160_s3_ll.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane74 rev160_vertex4 rev160_vertex5 rev160_s3_ll
    rev160_vertex4_mem rev160_vertex5_mem (by decide)
def rev160_s3_lr : FractionPoint := ⟨216994696901067,296192993000000,1642088682618057,2073350951000000⟩
theorem rev160_s3_lr_mem : rev160_s3_lr.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane74 rev160_vertex4 rev160_vertex5 rev160_s3_lr
    rev160_vertex4_mem rev160_vertex5_mem (by decide)
def rev160_s3_ul : FractionPoint := ⟨167556390057181017,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev160_s3_ul_mem : rev160_s3_ul.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane19 rev160_vertex1 rev160_vertex0 rev160_s3_ul
    rev160_vertex1_mem rev160_vertex0_mem (by decide)
def rev160_s3_ur : FractionPoint := ⟨216994696901067,296192993000000,87487731771001536579,106638067076797000000⟩
theorem rev160_s3_ur_mem : rev160_s3_ur.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane19 rev160_vertex1 rev160_vertex0 rev160_s3_ur
    rev160_vertex1_mem rev160_vertex0_mem (by decide)
theorem rev160_slab3 (p : Point) (hp : p∈IntegerCarrier rev160_planes)
    (hx0 : rev160_s3_ll.real.1≤p.1) (hx1 : p.1≤rev160_s3_lr.real.1) :
    p∈rationalHull (fractionRow160.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev160_plane74 rev160_plane19 rev160_s3_ll rev160_s3_lr rev160_s3_ul rev160_s3_ur
    (by decide) rev160_s3_ll_mem rev160_s3_lr_mem rev160_s3_ul_mem rev160_s3_ur_mem p
    (hp _ rev160_plane74_mem) (hp _ rev160_plane19_mem) hx0 hx1
def rev160_s4_ll : FractionPoint := ⟨216994696901067,296192993000000,1642088682618057,2073350951000000⟩
theorem rev160_s4_ll_mem : rev160_s4_ll.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane79 rev160_vertex5 rev160_vertex0 rev160_s4_ll
    rev160_vertex5_mem rev160_vertex0_mem (by decide)
def rev160_s4_lr : FractionPoint := ⟨23768824866023187,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev160_s4_lr_mem : rev160_s4_lr.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane79 rev160_vertex5 rev160_vertex0 rev160_s4_lr
    rev160_vertex5_mem rev160_vertex0_mem (by decide)
def rev160_s4_ul : FractionPoint := ⟨216994696901067,296192993000000,87487731771001536579,106638067076797000000⟩
theorem rev160_s4_ul_mem : rev160_s4_ul.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane19 rev160_vertex1 rev160_vertex0 rev160_s4_ul
    rev160_vertex1_mem rev160_vertex0_mem (by decide)
def rev160_s4_ur : FractionPoint := ⟨23768824866023187,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev160_s4_ur_mem : rev160_s4_ur.real ∈ rationalHull (fractionRow160.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow160 rev160_plane19 rev160_vertex1 rev160_vertex0 rev160_s4_ur
    rev160_vertex1_mem rev160_vertex0_mem (by decide)
theorem rev160_slab4 (p : Point) (hp : p∈IntegerCarrier rev160_planes)
    (hx0 : rev160_s4_ll.real.1≤p.1) (hx1 : p.1≤rev160_s4_lr.real.1) :
    p∈rationalHull (fractionRow160.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev160_plane79 rev160_plane19 rev160_s4_ll rev160_s4_lr rev160_s4_ul rev160_s4_ur
    (by decide) rev160_s4_ll_mem rev160_s4_lr_mem rev160_s4_ul_mem rev160_s4_ur_mem p
    (hp _ rev160_plane79_mem) (hp _ rev160_plane19_mem) hx0 hx1
theorem rev160_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev160_planes) : rev160_s0_ll.real.1≤p.1 := by
  have hc := rev160_plane48.combine_sound rev160_plane53 2044968000000 48252000000 (by decide) (by decide) p
    (hp _ rev160_plane48_mem) (hp _ rev160_plane53_mem)
  exact (rev160_plane48.combine rev160_plane53 2044968000000 48252000000).xBoundCheck_sound rev160_s0_ll.nx rev160_s0_ll.dx true (by decide) p hc
theorem rev160_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev160_planes) : p.1≤rev160_s4_lr.real.1 := by
  have hc := rev160_plane19.combine_sound rev160_plane79 15204000000 1440116000000 (by decide) (by decide) p
    (hp _ rev160_plane19_mem) (hp _ rev160_plane79_mem)
  exact (rev160_plane19.combine rev160_plane79 15204000000 1440116000000).xBoundCheck_sound rev160_s4_lr.nx rev160_s4_lr.dx false (by decide) p hc
theorem rev160_hull (p : Point) (hp : p∈IntegerCarrier rev160_planes) :
    p∈rationalHull (fractionRow160.map FractionPoint.rational) := by
  have hxlo := rev160_bound0_lo p hp
  have hxhi := rev160_bound0_hi p hp
  by_cases h0 : p.1≤rev160_s0_lr.real.1
  · exact rev160_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev160_s1_lr.real.1
  · exact rev160_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev160_s2_lr.real.1
  · exact rev160_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev160_s3_lr.real.1
  · exact rev160_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev160_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull160 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,13,8,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow160 := by
  rw [← fractionRow160_correct]
  exact rev160_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull160
