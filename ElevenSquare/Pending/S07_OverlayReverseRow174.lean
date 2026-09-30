import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks21
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev174_planes : List IntegerPlane := integerOverlayPlanes ![11,8,13,10]
def rev174_plane14 : IntegerPlane := ⟨(-2144520000000),699568000000,(-1185942108648)⟩
theorem rev174_plane14_mem : rev174_plane14 ∈ rev174_planes := by decide
def rev174_plane19 : IntegerPlane := ⟨(-15204000000),2139684000000,1555517771568⟩
theorem rev174_plane19_mem : rev174_plane19 ∈ rev174_planes := by decide
def rev174_plane28 : IntegerPlane := ⟨48252000000,(-2112760000000),(-1081757250915)⟩
theorem rev174_plane28_mem : rev174_plane28 ∈ rev174_planes := by decide
def rev174_plane33 : IntegerPlane := ⟨(-2044968000000),(-643972000000),(-1962432524019)⟩
theorem rev174_plane33_mem : rev174_plane33 ∈ rev174_planes := by decide
def rev174_plane78 : IntegerPlane := ⟨2139440000000,(-16372000000),1745735152575⟩
theorem rev174_plane78_mem : rev174_plane78 ∈ rev174_planes := by decide
def rev174_plane79 : IntegerPlane := ⟨1440116000000,2129316000000,2741459880216⟩
theorem rev174_plane79_mem : rev174_plane79 ∈ rev174_planes := by decide
def rev174_vertex0 : FractionPoint := fractionRow174[0]!
theorem rev174_vertex0_mem : rev174_vertex0∈fractionRow174 := by decide
def rev174_vertex1 : FractionPoint := fractionRow174[1]!
theorem rev174_vertex1_mem : rev174_vertex1∈fractionRow174 := by decide
def rev174_vertex2 : FractionPoint := fractionRow174[2]!
theorem rev174_vertex2_mem : rev174_vertex2∈fractionRow174 := by decide
def rev174_vertex3 : FractionPoint := fractionRow174[3]!
theorem rev174_vertex3_mem : rev174_vertex3∈fractionRow174 := by decide
def rev174_vertex4 : FractionPoint := fractionRow174[4]!
theorem rev174_vertex4_mem : rev174_vertex4∈fractionRow174 := by decide
def rev174_vertex5 : FractionPoint := fractionRow174[5]!
theorem rev174_vertex5_mem : rev174_vertex5∈fractionRow174 := by decide
def rev174_s0_ll : FractionPoint := ⟨1935297561189487,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev174_s0_ll_mem : rev174_s0_ll.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane33 rev174_vertex3 rev174_vertex4 rev174_s0_ll
    rev174_vertex3_mem rev174_vertex4_mem (by decide)
def rev174_s0_lr : FractionPoint := ⟨1642088682618057,2073350951000000,710792530832041204893,1335179958617372000000⟩
theorem rev174_s0_lr_mem : rev174_s0_lr.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane33 rev174_vertex3 rev174_vertex4 rev174_s0_lr
    rev174_vertex3_mem rev174_vertex4_mem (by decide)
def rev174_s0_ul : FractionPoint := ⟨1935297561189487,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev174_s0_ul_mem : rev174_s0_ul.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane14 rev174_vertex3 rev174_vertex2 rev174_s0_ul
    rev174_vertex3_mem rev174_vertex2_mem (by decide)
def rev174_s0_ur : FractionPoint := ⟨1642088682618057,2073350951000000,216994696901067,296192993000000⟩
theorem rev174_s0_ur_mem : rev174_s0_ur.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane14 rev174_vertex3 rev174_vertex2 rev174_s0_ur
    rev174_vertex3_mem rev174_vertex2_mem (by decide)
theorem rev174_slab0 (p : Point) (hp : p∈IntegerCarrier rev174_planes)
    (hx0 : rev174_s0_ll.real.1≤p.1) (hx1 : p.1≤rev174_s0_lr.real.1) :
    p∈rationalHull (fractionRow174.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev174_plane33 rev174_plane14 rev174_s0_ll rev174_s0_lr rev174_s0_ul rev174_s0_ur
    (by decide) rev174_s0_ll_mem rev174_s0_lr_mem rev174_s0_ul_mem rev174_s0_ur_mem p
    (hp _ rev174_plane33_mem) (hp _ rev174_plane14_mem) hx0 hx1
def rev174_s1_ll : FractionPoint := ⟨1642088682618057,2073350951000000,710792530832041204893,1335179958617372000000⟩
theorem rev174_s1_ll_mem : rev174_s1_ll.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane33 rev174_vertex3 rev174_vertex4 rev174_s1_ll
    rev174_vertex3_mem rev174_vertex4_mem (by decide)
def rev174_s1_lr : FractionPoint := ⟨57492125984335801,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev174_s1_lr_mem : rev174_s1_lr.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane33 rev174_vertex3 rev174_vertex4 rev174_s1_lr
    rev174_vertex3_mem rev174_vertex4_mem (by decide)
def rev174_s1_ul : FractionPoint := ⟨1642088682618057,2073350951000000,216994696901067,296192993000000⟩
theorem rev174_s1_ul_mem : rev174_s1_ul.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane19 rev174_vertex2 rev174_vertex1 rev174_s1_ul
    rev174_vertex2_mem rev174_vertex1_mem (by decide)
def rev174_s1_ur : FractionPoint := ⟨57492125984335801,72526658810400000,47371090406454959725463,64660054762529964000000⟩
theorem rev174_s1_ur_mem : rev174_s1_ur.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane19 rev174_vertex2 rev174_vertex1 rev174_s1_ur
    rev174_vertex2_mem rev174_vertex1_mem (by decide)
theorem rev174_slab1 (p : Point) (hp : p∈IntegerCarrier rev174_planes)
    (hx0 : rev174_s1_ll.real.1≤p.1) (hx1 : p.1≤rev174_s1_lr.real.1) :
    p∈rationalHull (fractionRow174.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev174_plane33 rev174_plane19 rev174_s1_ll rev174_s1_lr rev174_s1_ul rev174_s1_ur
    (by decide) rev174_s1_ll_mem rev174_s1_lr_mem rev174_s1_ul_mem rev174_s1_ur_mem p
    (hp _ rev174_plane33_mem) (hp _ rev174_plane19_mem) hx0 hx1
def rev174_s2_ll : FractionPoint := ⟨57492125984335801,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev174_s2_ll_mem : rev174_s2_ll.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane28 rev174_vertex4 rev174_vertex5 rev174_s2_ll
    rev174_vertex4_mem rev174_vertex5_mem (by decide)
def rev174_s2_lr : FractionPoint := ⟨185301496533316869,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev174_s2_lr_mem : rev174_s2_lr.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane28 rev174_vertex4 rev174_vertex5 rev174_s2_lr
    rev174_vertex4_mem rev174_vertex5_mem (by decide)
def rev174_s2_ul : FractionPoint := ⟨57492125984335801,72526658810400000,47371090406454959725463,64660054762529964000000⟩
theorem rev174_s2_ul_mem : rev174_s2_ul.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane19 rev174_vertex2 rev174_vertex1 rev174_s2_ul
    rev174_vertex2_mem rev174_vertex1_mem (by decide)
def rev174_s2_ur : FractionPoint := ⟨185301496533316869,225966663632800000,147630202090017263795211,201457189461868348000000⟩
theorem rev174_s2_ur_mem : rev174_s2_ur.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane19 rev174_vertex2 rev174_vertex1 rev174_s2_ur
    rev174_vertex2_mem rev174_vertex1_mem (by decide)
theorem rev174_slab2 (p : Point) (hp : p∈IntegerCarrier rev174_planes)
    (hx0 : rev174_s2_ll.real.1≤p.1) (hx1 : p.1≤rev174_s2_lr.real.1) :
    p∈rationalHull (fractionRow174.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev174_plane28 rev174_plane19 rev174_s2_ll rev174_s2_lr rev174_s2_ul rev174_s2_ur
    (by decide) rev174_s2_ll_mem rev174_s2_lr_mem rev174_s2_ul_mem rev174_s2_ur_mem p
    (hp _ rev174_plane28_mem) (hp _ rev174_plane19_mem) hx0 hx1
def rev174_s3_ll : FractionPoint := ⟨185301496533316869,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev174_s3_ll_mem : rev174_s3_ll.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane78 rev174_vertex5 rev174_vertex0 rev174_s3_ll
    rev174_vertex5_mem rev174_vertex0_mem (by decide)
def rev174_s3_lr : FractionPoint := ⟨26600718365166711,32435075873000000,57517754247782371773,106205412438551200000⟩
theorem rev174_s3_lr_mem : rev174_s3_lr.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane78 rev174_vertex5 rev174_vertex0 rev174_s3_lr
    rev174_vertex5_mem rev174_vertex0_mem (by decide)
def rev174_s3_ul : FractionPoint := ⟨185301496533316869,225966663632800000,147630202090017263795211,201457189461868348000000⟩
theorem rev174_s3_ul_mem : rev174_s3_ul.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane19 rev174_vertex2 rev174_vertex1 rev174_s3_ul
    rev174_vertex2_mem rev174_vertex1_mem (by decide)
def rev174_s3_ur : FractionPoint := ⟨26600718365166711,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev174_s3_ur_mem : rev174_s3_ur.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane19 rev174_vertex2 rev174_vertex1 rev174_s3_ur
    rev174_vertex2_mem rev174_vertex1_mem (by decide)
theorem rev174_slab3 (p : Point) (hp : p∈IntegerCarrier rev174_planes)
    (hx0 : rev174_s3_ll.real.1≤p.1) (hx1 : p.1≤rev174_s3_lr.real.1) :
    p∈rationalHull (fractionRow174.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev174_plane78 rev174_plane19 rev174_s3_ll rev174_s3_lr rev174_s3_ul rev174_s3_ur
    (by decide) rev174_s3_ll_mem rev174_s3_lr_mem rev174_s3_ul_mem rev174_s3_ur_mem p
    (hp _ rev174_plane78_mem) (hp _ rev174_plane19_mem) hx0 hx1
def rev174_s4_ll : FractionPoint := ⟨26600718365166711,32435075873000000,57517754247782371773,106205412438551200000⟩
theorem rev174_s4_ll_mem : rev174_s4_ll.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane78 rev174_vertex5 rev174_vertex0 rev174_s4_ll
    rev174_vertex5_mem rev174_vertex0_mem (by decide)
def rev174_s4_lr : FractionPoint := ⟨940526243324821263,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev174_s4_lr_mem : rev174_s4_lr.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane78 rev174_vertex5 rev174_vertex0 rev174_s4_lr
    rev174_vertex5_mem rev174_vertex0_mem (by decide)
def rev174_s4_ul : FractionPoint := ⟨26600718365166711,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev174_s4_ul_mem : rev174_s4_ul.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane79 rev174_vertex1 rev174_vertex0 rev174_s4_ul
    rev174_vertex1_mem rev174_vertex0_mem (by decide)
def rev174_s4_ur : FractionPoint := ⟨940526243324821263,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev174_s4_ur_mem : rev174_s4_ur.real ∈ rationalHull (fractionRow174.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow174 rev174_plane79 rev174_vertex1 rev174_vertex0 rev174_s4_ur
    rev174_vertex1_mem rev174_vertex0_mem (by decide)
theorem rev174_slab4 (p : Point) (hp : p∈IntegerCarrier rev174_planes)
    (hx0 : rev174_s4_ll.real.1≤p.1) (hx1 : p.1≤rev174_s4_lr.real.1) :
    p∈rationalHull (fractionRow174.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev174_plane78 rev174_plane79 rev174_s4_ll rev174_s4_lr rev174_s4_ul rev174_s4_ur
    (by decide) rev174_s4_ll_mem rev174_s4_lr_mem rev174_s4_ul_mem rev174_s4_ur_mem p
    (hp _ rev174_plane78_mem) (hp _ rev174_plane79_mem) hx0 hx1
theorem rev174_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev174_planes) : rev174_s0_ll.real.1≤p.1 := by
  have hc := rev174_plane14.combine_sound rev174_plane33 643972000000 699568000000 (by decide) (by decide) p
    (hp _ rev174_plane14_mem) (hp _ rev174_plane33_mem)
  exact (rev174_plane14.combine rev174_plane33 643972000000 699568000000).xBoundCheck_sound rev174_s0_ll.nx rev174_s0_ll.dx true (by decide) p hc
theorem rev174_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev174_planes) : p.1≤rev174_s4_lr.real.1 := by
  have hc := rev174_plane78.combine_sound rev174_plane79 2129316000000 16372000000 (by decide) (by decide) p
    (hp _ rev174_plane78_mem) (hp _ rev174_plane79_mem)
  exact (rev174_plane78.combine rev174_plane79 2129316000000 16372000000).xBoundCheck_sound rev174_s4_lr.nx rev174_s4_lr.dx false (by decide) p hc
theorem rev174_hull (p : Point) (hp : p∈IntegerCarrier rev174_planes) :
    p∈rationalHull (fractionRow174.map FractionPoint.rational) := by
  have hxlo := rev174_bound0_lo p hp
  have hxhi := rev174_bound0_hi p hp
  by_cases h0 : p.1≤rev174_s0_lr.real.1
  · exact rev174_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev174_s1_lr.real.1
  · exact rev174_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev174_s2_lr.real.1
  · exact rev174_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev174_s3_lr.real.1
  · exact rev174_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev174_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull174 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,8,13,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow174 := by
  rw [← fractionRow174_correct]
  exact rev174_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull174
