import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks14
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev118_planes : List IntegerPlane := integerOverlayPlanes ![8,11,5,2]
def rev118_plane8 : IntegerPlane := ⟨(-48252000000),(-2112760000000),(-1130009250915)⟩
theorem rev118_plane8_mem : rev118_plane8 ∈ rev118_planes := by decide
def rev118_plane13 : IntegerPlane := ⟨2044968000000,(-643972000000),82535475981⟩
theorem rev118_plane13_mem : rev118_plane13 ∈ rev118_planes := by decide
def rev118_plane34 : IntegerPlane := ⟨2144520000000,699568000000,958577891352⟩
theorem rev118_plane34_mem : rev118_plane34 ∈ rev118_planes := by decide
def rev118_plane39 : IntegerPlane := ⟨15204000000,2139684000000,1570721771568⟩
theorem rev118_plane39_mem : rev118_plane39 ∈ rev118_planes := by decide
def rev118_plane44 : IntegerPlane := ⟨(-1440116000000),2129316000000,1301343880216⟩
theorem rev118_plane44_mem : rev118_plane44 ∈ rev118_planes := by decide
def rev118_plane45 : IntegerPlane := ⟨(-2139440000000),(-16372000000),(-393704847425)⟩
theorem rev118_plane45_mem : rev118_plane45 ∈ rev118_planes := by decide
def rev118_vertex0 : FractionPoint := fractionRow118[0]!
theorem rev118_vertex0_mem : rev118_vertex0∈fractionRow118 := by decide
def rev118_vertex1 : FractionPoint := fractionRow118[1]!
theorem rev118_vertex1_mem : rev118_vertex1∈fractionRow118 := by decide
def rev118_vertex2 : FractionPoint := fractionRow118[2]!
theorem rev118_vertex2_mem : rev118_vertex2∈fractionRow118 := by decide
def rev118_vertex3 : FractionPoint := fractionRow118[3]!
theorem rev118_vertex3_mem : rev118_vertex3∈fractionRow118 := by decide
def rev118_vertex4 : FractionPoint := fractionRow118[4]!
theorem rev118_vertex4_mem : rev118_vertex4∈fractionRow118 := by decide
def rev118_vertex5 : FractionPoint := fractionRow118[5]!
theorem rev118_vertex5_mem : rev118_vertex5∈fractionRow118 := by decide
def rev118_s0_ll : FractionPoint := ⟨204254107223178737,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev118_s0_ll_mem : rev118_s0_ll.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane45 rev118_vertex5 rev118_vertex0 rev118_s0_ll
    rev118_vertex5_mem rev118_vertex0_mem (by decide)
def rev118_s0_lr : FractionPoint := ⟨5834357507833289,32435075873000000,57517754247782371773,106205412438551200000⟩
theorem rev118_s0_lr_mem : rev118_s0_lr.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane45 rev118_vertex5 rev118_vertex0 rev118_s0_lr
    rev118_vertex5_mem rev118_vertex0_mem (by decide)
def rev118_s0_ul : FractionPoint := ⟨204254107223178737,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev118_s0_ul_mem : rev118_s0_ul.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane44 rev118_vertex5 rev118_vertex4 rev118_s0_ul
    rev118_vertex5_mem rev118_vertex4_mem (by decide)
def rev118_s0_ur : FractionPoint := ⟨5834357507833289,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev118_s0_ur_mem : rev118_s0_ur.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane44 rev118_vertex5 rev118_vertex4 rev118_s0_ur
    rev118_vertex5_mem rev118_vertex4_mem (by decide)
theorem rev118_slab0 (p : Point) (hp : p∈IntegerCarrier rev118_planes)
    (hx0 : rev118_s0_ll.real.1≤p.1) (hx1 : p.1≤rev118_s0_lr.real.1) :
    p∈rationalHull (fractionRow118.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev118_plane45 rev118_plane44 rev118_s0_ll rev118_s0_lr rev118_s0_ul rev118_s0_ur
    (by decide) rev118_s0_ll_mem rev118_s0_lr_mem rev118_s0_ul_mem rev118_s0_ur_mem p
    (hp _ rev118_plane45_mem) (hp _ rev118_plane44_mem) hx0 hx1
def rev118_s1_ll : FractionPoint := ⟨5834357507833289,32435075873000000,57517754247782371773,106205412438551200000⟩
theorem rev118_s1_ll_mem : rev118_s1_ll.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane45 rev118_vertex5 rev118_vertex0 rev118_s1_ll
    rev118_vertex5_mem rev118_vertex0_mem (by decide)
def rev118_s1_lr : FractionPoint := ⟨40665167099483131,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev118_s1_lr_mem : rev118_s1_lr.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane45 rev118_vertex5 rev118_vertex0 rev118_s1_lr
    rev118_vertex5_mem rev118_vertex0_mem (by decide)
def rev118_s1_ul : FractionPoint := ⟨5834357507833289,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev118_s1_ul_mem : rev118_s1_ul.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane39 rev118_vertex4 rev118_vertex3 rev118_s1_ul
    rev118_vertex4_mem rev118_vertex3_mem (by decide)
def rev118_s1_ur : FractionPoint := ⟨40665167099483131,225966663632800000,147630202090017263795211,201457189461868348000000⟩
theorem rev118_s1_ur_mem : rev118_s1_ur.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane39 rev118_vertex4 rev118_vertex3 rev118_s1_ur
    rev118_vertex4_mem rev118_vertex3_mem (by decide)
theorem rev118_slab1 (p : Point) (hp : p∈IntegerCarrier rev118_planes)
    (hx0 : rev118_s1_ll.real.1≤p.1) (hx1 : p.1≤rev118_s1_lr.real.1) :
    p∈rationalHull (fractionRow118.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev118_plane45 rev118_plane39 rev118_s1_ll rev118_s1_lr rev118_s1_ul rev118_s1_ur
    (by decide) rev118_s1_ll_mem rev118_s1_lr_mem rev118_s1_ul_mem rev118_s1_ur_mem p
    (hp _ rev118_plane45_mem) (hp _ rev118_plane39_mem) hx0 hx1
def rev118_s2_ll : FractionPoint := ⟨40665167099483131,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev118_s2_ll_mem : rev118_s2_ll.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane8 rev118_vertex0 rev118_vertex1 rev118_s2_ll
    rev118_vertex0_mem rev118_vertex1_mem (by decide)
def rev118_s2_lr : FractionPoint := ⟨15034532826064199,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev118_s2_lr_mem : rev118_s2_lr.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane8 rev118_vertex0 rev118_vertex1 rev118_s2_lr
    rev118_vertex0_mem rev118_vertex1_mem (by decide)
def rev118_s2_ul : FractionPoint := ⟨40665167099483131,225966663632800000,147630202090017263795211,201457189461868348000000⟩
theorem rev118_s2_ul_mem : rev118_s2_ul.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane39 rev118_vertex4 rev118_vertex3 rev118_s2_ul
    rev118_vertex4_mem rev118_vertex3_mem (by decide)
def rev118_s2_ur : FractionPoint := ⟨15034532826064199,72526658810400000,47371090406454959725463,64660054762529964000000⟩
theorem rev118_s2_ur_mem : rev118_s2_ur.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane39 rev118_vertex4 rev118_vertex3 rev118_s2_ur
    rev118_vertex4_mem rev118_vertex3_mem (by decide)
theorem rev118_slab2 (p : Point) (hp : p∈IntegerCarrier rev118_planes)
    (hx0 : rev118_s2_ll.real.1≤p.1) (hx1 : p.1≤rev118_s2_lr.real.1) :
    p∈rationalHull (fractionRow118.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev118_plane8 rev118_plane39 rev118_s2_ll rev118_s2_lr rev118_s2_ul rev118_s2_ur
    (by decide) rev118_s2_ll_mem rev118_s2_lr_mem rev118_s2_ul_mem rev118_s2_ur_mem p
    (hp _ rev118_plane8_mem) (hp _ rev118_plane39_mem) hx0 hx1
def rev118_s3_ll : FractionPoint := ⟨15034532826064199,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev118_s3_ll_mem : rev118_s3_ll.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane13 rev118_vertex1 rev118_vertex2 rev118_s3_ll
    rev118_vertex1_mem rev118_vertex2_mem (by decide)
def rev118_s3_lr : FractionPoint := ⟨431262268381943,2073350951000000,710792530832041204893,1335179958617372000000⟩
theorem rev118_s3_lr_mem : rev118_s3_lr.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane13 rev118_vertex1 rev118_vertex2 rev118_s3_lr
    rev118_vertex1_mem rev118_vertex2_mem (by decide)
def rev118_s3_ul : FractionPoint := ⟨15034532826064199,72526658810400000,47371090406454959725463,64660054762529964000000⟩
theorem rev118_s3_ul_mem : rev118_s3_ul.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane39 rev118_vertex4 rev118_vertex3 rev118_s3_ul
    rev118_vertex4_mem rev118_vertex3_mem (by decide)
def rev118_s3_ur : FractionPoint := ⟨431262268381943,2073350951000000,216994696901067,296192993000000⟩
theorem rev118_s3_ur_mem : rev118_s3_ur.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane39 rev118_vertex4 rev118_vertex3 rev118_s3_ur
    rev118_vertex4_mem rev118_vertex3_mem (by decide)
theorem rev118_slab3 (p : Point) (hp : p∈IntegerCarrier rev118_planes)
    (hx0 : rev118_s3_ll.real.1≤p.1) (hx1 : p.1≤rev118_s3_lr.real.1) :
    p∈rationalHull (fractionRow118.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev118_plane13 rev118_plane39 rev118_s3_ll rev118_s3_lr rev118_s3_ul rev118_s3_ur
    (by decide) rev118_s3_ll_mem rev118_s3_lr_mem rev118_s3_ul_mem rev118_s3_ur_mem p
    (hp _ rev118_plane13_mem) (hp _ rev118_plane39_mem) hx0 hx1
def rev118_s4_ll : FractionPoint := ⟨431262268381943,2073350951000000,710792530832041204893,1335179958617372000000⟩
theorem rev118_s4_ll_mem : rev118_s4_ll.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane13 rev118_vertex1 rev118_vertex2 rev118_s4_ll
    rev118_vertex1_mem rev118_vertex2_mem (by decide)
def rev118_s4_lr : FractionPoint := ⟨611446104810513,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev118_s4_lr_mem : rev118_s4_lr.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane13 rev118_vertex1 rev118_vertex2 rev118_s4_lr
    rev118_vertex1_mem rev118_vertex2_mem (by decide)
def rev118_s4_ul : FractionPoint := ⟨431262268381943,2073350951000000,216994696901067,296192993000000⟩
theorem rev118_s4_ul_mem : rev118_s4_ul.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane34 rev118_vertex3 rev118_vertex2 rev118_s4_ul
    rev118_vertex3_mem rev118_vertex2_mem (by decide)
def rev118_s4_ur : FractionPoint := ⟨611446104810513,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev118_s4_ur_mem : rev118_s4_ur.real ∈ rationalHull (fractionRow118.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow118 rev118_plane34 rev118_vertex3 rev118_vertex2 rev118_s4_ur
    rev118_vertex3_mem rev118_vertex2_mem (by decide)
theorem rev118_slab4 (p : Point) (hp : p∈IntegerCarrier rev118_planes)
    (hx0 : rev118_s4_ll.real.1≤p.1) (hx1 : p.1≤rev118_s4_lr.real.1) :
    p∈rationalHull (fractionRow118.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev118_plane13 rev118_plane34 rev118_s4_ll rev118_s4_lr rev118_s4_ul rev118_s4_ur
    (by decide) rev118_s4_ll_mem rev118_s4_lr_mem rev118_s4_ul_mem rev118_s4_ur_mem p
    (hp _ rev118_plane13_mem) (hp _ rev118_plane34_mem) hx0 hx1
theorem rev118_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev118_planes) : rev118_s0_ll.real.1≤p.1 := by
  have hc := rev118_plane44.combine_sound rev118_plane45 16372000000 2129316000000 (by decide) (by decide) p
    (hp _ rev118_plane44_mem) (hp _ rev118_plane45_mem)
  exact (rev118_plane44.combine rev118_plane45 16372000000 2129316000000).xBoundCheck_sound rev118_s0_ll.nx rev118_s0_ll.dx true (by decide) p hc
theorem rev118_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev118_planes) : p.1≤rev118_s4_lr.real.1 := by
  have hc := rev118_plane13.combine_sound rev118_plane34 699568000000 643972000000 (by decide) (by decide) p
    (hp _ rev118_plane13_mem) (hp _ rev118_plane34_mem)
  exact (rev118_plane13.combine rev118_plane34 699568000000 643972000000).xBoundCheck_sound rev118_s4_lr.nx rev118_s4_lr.dx false (by decide) p hc
theorem rev118_hull (p : Point) (hp : p∈IntegerCarrier rev118_planes) :
    p∈rationalHull (fractionRow118.map FractionPoint.rational) := by
  have hxlo := rev118_bound0_lo p hp
  have hxhi := rev118_bound0_hi p hp
  by_cases h0 : p.1≤rev118_s0_lr.real.1
  · exact rev118_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev118_s1_lr.real.1
  · exact rev118_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev118_s2_lr.real.1
  · exact rev118_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev118_s3_lr.real.1
  · exact rev118_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev118_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull118 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,11,5,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow118 := by
  rw [← fractionRow118_correct]
  exact rev118_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull118
