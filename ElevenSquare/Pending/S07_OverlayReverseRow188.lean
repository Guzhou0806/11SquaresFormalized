import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks23
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev188_planes : List IntegerPlane := integerOverlayPlanes ![13,10,4,7]
def rev188_plane38 : IntegerPlane := ⟨16372000000,2139440000000,1762107152575⟩
theorem rev188_plane38_mem : rev188_plane38 ∈ rev188_planes := by decide
def rev188_plane39 : IntegerPlane := ⟨(-2129316000000),1440116000000,612143880216⟩
theorem rev188_plane39_mem : rev188_plane39 ∈ rev188_planes := by decide
def rev188_plane44 : IntegerPlane := ⟨(-2139684000000),(-15204000000),(-584166228432)⟩
theorem rev188_plane44_mem : rev188_plane44 ∈ rev188_planes := by decide
def rev188_plane49 : IntegerPlane := ⟨(-699568000000),(-2144520000000),(-1885510108648)⟩
theorem rev188_plane49_mem : rev188_plane49 ∈ rev188_planes := by decide
def rev188_plane70 : IntegerPlane := ⟨643972000000,(-2044968000000),(-1318460524019)⟩
theorem rev188_plane70_mem : rev188_plane70 ∈ rev188_planes := by decide
def rev188_plane75 : IntegerPlane := ⟨2112760000000,48252000000,1031002749085⟩
theorem rev188_plane75_mem : rev188_plane75 ∈ rev188_planes := by decide
def rev188_vertex0 : FractionPoint := fractionRow188[0]!
theorem rev188_vertex0_mem : rev188_vertex0∈fractionRow188 := by decide
def rev188_vertex1 : FractionPoint := fractionRow188[1]!
theorem rev188_vertex1_mem : rev188_vertex1∈fractionRow188 := by decide
def rev188_vertex2 : FractionPoint := fractionRow188[2]!
theorem rev188_vertex2_mem : rev188_vertex2∈fractionRow188 := by decide
def rev188_vertex3 : FractionPoint := fractionRow188[3]!
theorem rev188_vertex3_mem : rev188_vertex3∈fractionRow188 := by decide
def rev188_vertex4 : FractionPoint := fractionRow188[4]!
theorem rev188_vertex4_mem : rev188_vertex4∈fractionRow188 := by decide
def rev188_vertex5 : FractionPoint := fractionRow188[5]!
theorem rev188_vertex5_mem : rev188_vertex5∈fractionRow188 := by decide
def rev188_s0_ll : FractionPoint := ⟨8666251006976813,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev188_s0_ll_mem : rev188_s0_ll.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane44 rev188_vertex1 rev188_vertex2 rev188_s0_ll
    rev188_vertex1_mem rev188_vertex2_mem (by decide)
def rev188_s0_lr : FractionPoint := ⟨79198296098933,296192993000000,1642088682618057,2073350951000000⟩
theorem rev188_s0_lr_mem : rev188_s0_lr.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane44 rev188_vertex1 rev188_vertex2 rev188_s0_lr
    rev188_vertex1_mem rev188_vertex2_mem (by decide)
def rev188_s0_ul : FractionPoint := ⟨8666251006976813,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev188_s0_ul_mem : rev188_s0_ul.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane39 rev188_vertex1 rev188_vertex0 rev188_s0_ul
    rev188_vertex1_mem rev188_vertex0_mem (by decide)
def rev188_s0_ur : FractionPoint := ⟨79198296098933,296192993000000,87487731771001536579,106638067076797000000⟩
theorem rev188_s0_ur_mem : rev188_s0_ur.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane39 rev188_vertex1 rev188_vertex0 rev188_s0_ur
    rev188_vertex1_mem rev188_vertex0_mem (by decide)
theorem rev188_slab0 (p : Point) (hp : p∈IntegerCarrier rev188_planes)
    (hx0 : rev188_s0_ll.real.1≤p.1) (hx1 : p.1≤rev188_s0_lr.real.1) :
    p∈rationalHull (fractionRow188.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev188_plane44 rev188_plane39 rev188_s0_ll rev188_s0_lr rev188_s0_ul rev188_s0_ur
    (by decide) rev188_s0_ll_mem rev188_s0_lr_mem rev188_s0_ul_mem rev188_s0_ur_mem p
    (hp _ rev188_plane44_mem) (hp _ rev188_plane39_mem) hx0 hx1
def rev188_s1_ll : FractionPoint := ⟨79198296098933,296192993000000,1642088682618057,2073350951000000⟩
theorem rev188_s1_ll_mem : rev188_s1_ll.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane49 rev188_vertex2 rev188_vertex3 rev188_s1_ll
    rev188_vertex2_mem rev188_vertex3_mem (by decide)
def rev188_s1_lr : FractionPoint := ⟨61399680052418983,228956070109600000,1760623791906976259821,2223735830939490000000⟩
theorem rev188_s1_lr_mem : rev188_s1_lr.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane49 rev188_vertex2 rev188_vertex3 rev188_s1_lr
    rev188_vertex2_mem rev188_vertex3_mem (by decide)
def rev188_s1_ul : FractionPoint := ⟨79198296098933,296192993000000,87487731771001536579,106638067076797000000⟩
theorem rev188_s1_ul_mem : rev188_s1_ul.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane39 rev188_vertex1 rev188_vertex0 rev188_s1_ul
    rev188_vertex1_mem rev188_vertex0_mem (by decide)
def rev188_s1_ur : FractionPoint := ⟨61399680052418983,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev188_s1_ur_mem : rev188_s1_ur.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane39 rev188_vertex1 rev188_vertex0 rev188_s1_ur
    rev188_vertex1_mem rev188_vertex0_mem (by decide)
theorem rev188_slab1 (p : Point) (hp : p∈IntegerCarrier rev188_planes)
    (hx0 : rev188_s1_ll.real.1≤p.1) (hx1 : p.1≤rev188_s1_lr.real.1) :
    p∈rationalHull (fractionRow188.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev188_plane49 rev188_plane39 rev188_s1_ll rev188_s1_lr rev188_s1_ul rev188_s1_ur
    (by decide) rev188_s1_ll_mem rev188_s1_lr_mem rev188_s1_ul_mem rev188_s1_ur_mem p
    (hp _ rev188_plane49_mem) (hp _ rev188_plane39_mem) hx0 hx1
def rev188_s2_ll : FractionPoint := ⟨61399680052418983,228956070109600000,1760623791906976259821,2223735830939490000000⟩
theorem rev188_s2_ll_mem : rev188_s2_ll.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane49 rev188_vertex2 rev188_vertex3 rev188_s2_ll
    rev188_vertex2_mem rev188_vertex3_mem (by decide)
def rev188_s2_lr : FractionPoint := ⟨1862939987124017,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev188_s2_lr_mem : rev188_s2_lr.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane49 rev188_vertex2 rev188_vertex3 rev188_s2_lr
    rev188_vertex2_mem rev188_vertex3_mem (by decide)
def rev188_s2_ul : FractionPoint := ⟨61399680052418983,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev188_s2_ul_mem : rev188_s2_ul.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane38 rev188_vertex0 rev188_vertex5 rev188_s2_ul
    rev188_vertex0_mem rev188_vertex5_mem (by decide)
def rev188_s2_ur : FractionPoint := ⟨1862939987124017,5093487332000000,1118096300724769909197,1362151317196760000000⟩
theorem rev188_s2_ur_mem : rev188_s2_ur.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane38 rev188_vertex0 rev188_vertex5 rev188_s2_ur
    rev188_vertex0_mem rev188_vertex5_mem (by decide)
theorem rev188_slab2 (p : Point) (hp : p∈IntegerCarrier rev188_planes)
    (hx0 : rev188_s2_ll.real.1≤p.1) (hx1 : p.1≤rev188_s2_lr.real.1) :
    p∈rationalHull (fractionRow188.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev188_plane49 rev188_plane38 rev188_s2_ll rev188_s2_lr rev188_s2_ul rev188_s2_ur
    (by decide) rev188_s2_ll_mem rev188_s2_lr_mem rev188_s2_ul_mem rev188_s2_ur_mem p
    (hp _ rev188_plane49_mem) (hp _ rev188_plane38_mem) hx0 hx1
def rev188_s3_ll : FractionPoint := ⟨1862939987124017,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev188_s3_ll_mem : rev188_s3_ll.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane70 rev188_vertex3 rev188_vertex4 rev188_s3_ll
    rev188_vertex3_mem rev188_vertex4_mem (by decide)
def rev188_s3_lr : FractionPoint := ⟨4241486654352727,9038666545312000,76294394133030719997359,96269707540799948000000⟩
theorem rev188_s3_lr_mem : rev188_s3_lr.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane70 rev188_vertex3 rev188_vertex4 rev188_s3_lr
    rev188_vertex3_mem rev188_vertex4_mem (by decide)
def rev188_s3_ul : FractionPoint := ⟨1862939987124017,5093487332000000,1118096300724769909197,1362151317196760000000⟩
theorem rev188_s3_ul_mem : rev188_s3_ul.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane38 rev188_vertex0 rev188_vertex5 rev188_s3_ul
    rev188_vertex0_mem rev188_vertex5_mem (by decide)
def rev188_s3_ur : FractionPoint := ⟨4241486654352727,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev188_s3_ur_mem : rev188_s3_ur.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane38 rev188_vertex0 rev188_vertex5 rev188_s3_ur
    rev188_vertex0_mem rev188_vertex5_mem (by decide)
theorem rev188_slab3 (p : Point) (hp : p∈IntegerCarrier rev188_planes)
    (hx0 : rev188_s3_ll.real.1≤p.1) (hx1 : p.1≤rev188_s3_lr.real.1) :
    p∈rationalHull (fractionRow188.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev188_plane70 rev188_plane38 rev188_s3_ll rev188_s3_lr rev188_s3_ul rev188_s3_ur
    (by decide) rev188_s3_ll_mem rev188_s3_lr_mem rev188_s3_ul_mem rev188_s3_ur_mem p
    (hp _ rev188_plane70_mem) (hp _ rev188_plane38_mem) hx0 hx1
def rev188_s4_ll : FractionPoint := ⟨4241486654352727,9038666545312000,76294394133030719997359,96269707540799948000000⟩
theorem rev188_s4_ll_mem : rev188_s4_ll.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane70 rev188_vertex3 rev188_vertex4 rev188_s4_ll
    rev188_vertex3_mem rev188_vertex4_mem (by decide)
def rev188_s4_lr : FractionPoint := ⟨56798590905163597,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev188_s4_lr_mem : rev188_s4_lr.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane70 rev188_vertex3 rev188_vertex4 rev188_s4_lr
    rev188_vertex3_mem rev188_vertex4_mem (by decide)
def rev188_s4_ul : FractionPoint := ⟨4241486654352727,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev188_s4_ul_mem : rev188_s4_ul.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane75 rev188_vertex5 rev188_vertex4 rev188_s4_ul
    rev188_vertex5_mem rev188_vertex4_mem (by decide)
def rev188_s4_ur : FractionPoint := ⟨56798590905163597,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev188_s4_ur_mem : rev188_s4_ur.real ∈ rationalHull (fractionRow188.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow188 rev188_plane75 rev188_vertex5 rev188_vertex4 rev188_s4_ur
    rev188_vertex5_mem rev188_vertex4_mem (by decide)
theorem rev188_slab4 (p : Point) (hp : p∈IntegerCarrier rev188_planes)
    (hx0 : rev188_s4_ll.real.1≤p.1) (hx1 : p.1≤rev188_s4_lr.real.1) :
    p∈rationalHull (fractionRow188.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev188_plane70 rev188_plane75 rev188_s4_ll rev188_s4_lr rev188_s4_ul rev188_s4_ur
    (by decide) rev188_s4_ll_mem rev188_s4_lr_mem rev188_s4_ul_mem rev188_s4_ur_mem p
    (hp _ rev188_plane70_mem) (hp _ rev188_plane75_mem) hx0 hx1
theorem rev188_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev188_planes) : rev188_s0_ll.real.1≤p.1 := by
  have hc := rev188_plane39.combine_sound rev188_plane44 15204000000 1440116000000 (by decide) (by decide) p
    (hp _ rev188_plane39_mem) (hp _ rev188_plane44_mem)
  exact (rev188_plane39.combine rev188_plane44 15204000000 1440116000000).xBoundCheck_sound rev188_s0_ll.nx rev188_s0_ll.dx true (by decide) p hc
theorem rev188_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev188_planes) : p.1≤rev188_s4_lr.real.1 := by
  have hc := rev188_plane70.combine_sound rev188_plane75 48252000000 2044968000000 (by decide) (by decide) p
    (hp _ rev188_plane70_mem) (hp _ rev188_plane75_mem)
  exact (rev188_plane70.combine rev188_plane75 48252000000 2044968000000).xBoundCheck_sound rev188_s4_lr.nx rev188_s4_lr.dx false (by decide) p hc
theorem rev188_hull (p : Point) (hp : p∈IntegerCarrier rev188_planes) :
    p∈rationalHull (fractionRow188.map FractionPoint.rational) := by
  have hxlo := rev188_bound0_lo p hp
  have hxhi := rev188_bound0_hi p hp
  by_cases h0 : p.1≤rev188_s0_lr.real.1
  · exact rev188_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev188_s1_lr.real.1
  · exact rev188_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev188_s2_lr.real.1
  · exact rev188_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev188_s3_lr.real.1
  · exact rev188_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev188_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull188 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,10,4,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow188 := by
  rw [← fractionRow188_correct]
  exact rev188_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull188
