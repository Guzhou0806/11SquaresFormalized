import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks2
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev23_planes : List IntegerPlane := integerOverlayPlanes ![2,1,11,8]
def rev23_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev23_plane2_mem : rev23_plane2 ∈ rev23_planes := by decide
def rev23_plane5 : IntegerPlane := ⟨(-2083356000000),(-746024000000),(-1117516707941)⟩
theorem rev23_plane5_mem : rev23_plane5 ∈ rev23_planes := by decide
def rev23_plane7 : IntegerPlane := ⟨1855520000000,(-287616000000),1356143759600⟩
theorem rev23_plane7_mem : rev23_plane7 ∈ rev23_planes := by decide
def rev23_plane24 : IntegerPlane := ⟨2145688000000,699324000000,1695048727641⟩
theorem rev23_plane24_mem : rev23_plane24 ∈ rev23_planes := by decide
def rev23_plane29 : IntegerPlane := ⟨16372000000,2139440000000,393704847425⟩
theorem rev23_plane29_mem : rev23_plane29 ∈ rev23_planes := by decide
def rev23_plane59 : IntegerPlane := ⟨2139684000000,15204000000,1570721771568⟩
theorem rev23_plane59_mem : rev23_plane59 ∈ rev23_planes := by decide
def rev23_plane68 : IntegerPlane := ⟨(-2112760000000),(-48252000000),(-1130009250915)⟩
theorem rev23_plane68_mem : rev23_plane68 ∈ rev23_planes := by decide
def rev23_vertex0 : FractionPoint := fractionRow23[0]!
theorem rev23_vertex0_mem : rev23_vertex0∈fractionRow23 := by decide
def rev23_vertex1 : FractionPoint := fractionRow23[1]!
theorem rev23_vertex1_mem : rev23_vertex1∈fractionRow23 := by decide
def rev23_vertex2 : FractionPoint := fractionRow23[2]!
theorem rev23_vertex2_mem : rev23_vertex2∈fractionRow23 := by decide
def rev23_vertex3 : FractionPoint := fractionRow23[3]!
theorem rev23_vertex3_mem : rev23_vertex3∈fractionRow23 := by decide
def rev23_vertex4 : FractionPoint := fractionRow23[4]!
theorem rev23_vertex4_mem : rev23_vertex4∈fractionRow23 := by decide
def rev23_vertex5 : FractionPoint := fractionRow23[5]!
theorem rev23_vertex5_mem : rev23_vertex5∈fractionRow23 := by decide
def rev23_vertex6 : FractionPoint := fractionRow23[6]!
theorem rev23_vertex6_mem : rev23_vertex6∈fractionRow23 := by decide
def rev23_s0_ll : FractionPoint := ⟨4797179890959273,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev23_s0_ll_mem : rev23_s0_ll.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane68 rev23_vertex5 rev23_vertex6 rev23_s0_ll
    rev23_vertex5_mem rev23_vertex6_mem (by decide)
def rev23_s0_lr : FractionPoint := ⟨197272901303260707,368910893132000000,341652346007821,73782178626400000⟩
theorem rev23_s0_lr_mem : rev23_s0_lr.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane68 rev23_vertex5 rev23_vertex6 rev23_s0_lr
    rev23_vertex5_mem rev23_vertex6_mem (by decide)
def rev23_s0_ul : FractionPoint := ⟨4797179890959273,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev23_s0_ul_mem : rev23_s0_ul.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane29 rev23_vertex5 rev23_vertex4 rev23_s0_ul
    rev23_vertex5_mem rev23_vertex4_mem (by decide)
def rev23_s0_ur : FractionPoint := ⟨197272901303260707,368910893132000000,8875765934613597255631,49328920075145380000000⟩
theorem rev23_s0_ur_mem : rev23_s0_ur.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane29 rev23_vertex5 rev23_vertex4 rev23_s0_ur
    rev23_vertex5_mem rev23_vertex4_mem (by decide)
theorem rev23_slab0 (p : Point) (hp : p∈IntegerCarrier rev23_planes)
    (hx0 : rev23_s0_ll.real.1≤p.1) (hx1 : p.1≤rev23_s0_lr.real.1) :
    p∈rationalHull (fractionRow23.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev23_plane68 rev23_plane29 rev23_s0_ll rev23_s0_lr rev23_s0_ul rev23_s0_ur
    (by decide) rev23_s0_ll_mem rev23_s0_lr_mem rev23_s0_ul_mem rev23_s0_ur_mem p
    (hp _ rev23_plane68_mem) (hp _ rev23_plane29_mem) hx0 hx1
def rev23_s1_ll : FractionPoint := ⟨197272901303260707,368910893132000000,341652346007821,73782178626400000⟩
theorem rev23_s1_ll_mem : rev23_s1_ll.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane5 rev23_vertex6 rev23_vertex0 rev23_s1_ll
    rev23_vertex6_mem rev23_vertex0_mem (by decide)
def rev23_s1_lr : FractionPoint := ⟨1117516707941,2083356000000,0,1⟩
theorem rev23_s1_lr_mem : rev23_s1_lr.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane5 rev23_vertex6 rev23_vertex0 rev23_s1_lr
    rev23_vertex6_mem rev23_vertex0_mem (by decide)
def rev23_s1_ul : FractionPoint := ⟨197272901303260707,368910893132000000,8875765934613597255631,49328920075145380000000⟩
theorem rev23_s1_ul_mem : rev23_s1_ul.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane29 rev23_vertex5 rev23_vertex4 rev23_s1_ul
    rev23_vertex5_mem rev23_vertex4_mem (by decide)
def rev23_s1_ur : FractionPoint := ⟨1117516707941,2083356000000,100241421571193531,557151895080000000⟩
theorem rev23_s1_ur_mem : rev23_s1_ur.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane29 rev23_vertex5 rev23_vertex4 rev23_s1_ur
    rev23_vertex5_mem rev23_vertex4_mem (by decide)
theorem rev23_slab1 (p : Point) (hp : p∈IntegerCarrier rev23_planes)
    (hx0 : rev23_s1_ll.real.1≤p.1) (hx1 : p.1≤rev23_s1_lr.real.1) :
    p∈rationalHull (fractionRow23.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev23_plane5 rev23_plane29 rev23_s1_ll rev23_s1_lr rev23_s1_ul rev23_s1_ur
    (by decide) rev23_s1_ll_mem rev23_s1_lr_mem rev23_s1_ul_mem rev23_s1_ur_mem p
    (hp _ rev23_plane5_mem) (hp _ rev23_plane29_mem) hx0 hx1
def rev23_s2_ll : FractionPoint := ⟨1117516707941,2083356000000,0,1⟩
theorem rev23_s2_ll_mem : rev23_s2_ll.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane2 rev23_vertex0 rev23_vertex1 rev23_s2_ll
    rev23_vertex0_mem rev23_vertex1_mem (by decide)
def rev23_s2_lr : FractionPoint := ⟨3390359399,4638800000,0,1⟩
theorem rev23_s2_lr_mem : rev23_s2_lr.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane2 rev23_vertex0 rev23_vertex1 rev23_s2_lr
    rev23_vertex0_mem rev23_vertex1_mem (by decide)
def rev23_s2_ul : FractionPoint := ⟨1117516707941,2083356000000,100241421571193531,557151895080000000⟩
theorem rev23_s2_ul_mem : rev23_s2_ul.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane29 rev23_vertex5 rev23_vertex4 rev23_s2_ul
    rev23_vertex5_mem rev23_vertex4_mem (by decide)
def rev23_s2_ur : FractionPoint := ⟨3390359399,4638800000,885405541077331,4962217136000000⟩
theorem rev23_s2_ur_mem : rev23_s2_ur.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane29 rev23_vertex5 rev23_vertex4 rev23_s2_ur
    rev23_vertex5_mem rev23_vertex4_mem (by decide)
theorem rev23_slab2 (p : Point) (hp : p∈IntegerCarrier rev23_planes)
    (hx0 : rev23_s2_ll.real.1≤p.1) (hx1 : p.1≤rev23_s2_lr.real.1) :
    p∈rationalHull (fractionRow23.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev23_plane2 rev23_plane29 rev23_s2_ll rev23_s2_lr rev23_s2_ul rev23_s2_ur
    (by decide) rev23_s2_ll_mem rev23_s2_lr_mem rev23_s2_ul_mem rev23_s2_ur_mem p
    (hp _ rev23_plane2_mem) (hp _ rev23_plane29_mem) hx0 hx1
def rev23_s3_ll : FractionPoint := ⟨3390359399,4638800000,0,1⟩
theorem rev23_s3_ll_mem : rev23_s3_ll.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane7 rev23_vertex1 rev23_vertex2 rev23_s3_ll
    rev23_vertex1_mem rev23_vertex2_mem (by decide)
def rev23_s3_lr : FractionPoint := ⟨167556390057181017,228956070109600000,2543044857664953823,411571431629016960000⟩
theorem rev23_s3_lr_mem : rev23_s3_lr.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane7 rev23_vertex1 rev23_vertex2 rev23_s3_lr
    rev23_vertex1_mem rev23_vertex2_mem (by decide)
def rev23_s3_ul : FractionPoint := ⟨3390359399,4638800000,885405541077331,4962217136000000⟩
theorem rev23_s3_ul_mem : rev23_s3_ul.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane29 rev23_vertex5 rev23_vertex4 rev23_s3_ul
    rev23_vertex5_mem rev23_vertex4_mem (by decide)
def rev23_s3_ur : FractionPoint := ⟨167556390057181017,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev23_s3_ur_mem : rev23_s3_ur.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane29 rev23_vertex5 rev23_vertex4 rev23_s3_ur
    rev23_vertex5_mem rev23_vertex4_mem (by decide)
theorem rev23_slab3 (p : Point) (hp : p∈IntegerCarrier rev23_planes)
    (hx0 : rev23_s3_ll.real.1≤p.1) (hx1 : p.1≤rev23_s3_lr.real.1) :
    p∈rationalHull (fractionRow23.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev23_plane7 rev23_plane29 rev23_s3_ll rev23_s3_lr rev23_s3_ul rev23_s3_ur
    (by decide) rev23_s3_ll_mem rev23_s3_lr_mem rev23_s3_ul_mem rev23_s3_ur_mem p
    (hp _ rev23_plane7_mem) (hp _ rev23_plane29_mem) hx0 hx1
def rev23_s4_ll : FractionPoint := ⟨167556390057181017,228956070109600000,2543044857664953823,411571431629016960000⟩
theorem rev23_s4_ll_mem : rev23_s4_ll.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane7 rev23_vertex1 rev23_vertex2 rev23_s4_ll
    rev23_vertex1_mem rev23_vertex2_mem (by decide)
def rev23_s4_lr : FractionPoint := ⟨89389325943747189,121975777772000000,2793701420547453263,219263658122947200000⟩
theorem rev23_s4_lr_mem : rev23_s4_lr.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane7 rev23_vertex1 rev23_vertex2 rev23_s4_lr
    rev23_vertex1_mem rev23_vertex2_mem (by decide)
def rev23_s4_ul : FractionPoint := ⟨167556390057181017,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev23_s4_ul_mem : rev23_s4_ul.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane24 rev23_vertex4 rev23_vertex3 rev23_s4_ul
    rev23_vertex4_mem rev23_vertex3_mem (by decide)
def rev23_s4_ur : FractionPoint := ⟨89389325943747189,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev23_s4_ur_mem : rev23_s4_ur.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane24 rev23_vertex4 rev23_vertex3 rev23_s4_ur
    rev23_vertex4_mem rev23_vertex3_mem (by decide)
theorem rev23_slab4 (p : Point) (hp : p∈IntegerCarrier rev23_planes)
    (hx0 : rev23_s4_ll.real.1≤p.1) (hx1 : p.1≤rev23_s4_lr.real.1) :
    p∈rationalHull (fractionRow23.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev23_plane7 rev23_plane24 rev23_s4_ll rev23_s4_lr rev23_s4_ul rev23_s4_ur
    (by decide) rev23_s4_ll_mem rev23_s4_lr_mem rev23_s4_ul_mem rev23_s4_ur_mem p
    (hp _ rev23_plane7_mem) (hp _ rev23_plane24_mem) hx0 hx1
def rev23_s5_ll : FractionPoint := ⟨89389325943747189,121975777772000000,2793701420547453263,219263658122947200000⟩
theorem rev23_s5_ll_mem : rev23_s5_ll.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane7 rev23_vertex1 rev23_vertex2 rev23_s5_ll
    rev23_vertex1_mem rev23_vertex2_mem (by decide)
def rev23_s5_lr : FractionPoint := ⟨351475835396027,478882946000000,13319330691551,670436124400000⟩
theorem rev23_s5_lr_mem : rev23_s5_lr.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane7 rev23_vertex1 rev23_vertex2 rev23_s5_lr
    rev23_vertex1_mem rev23_vertex2_mem (by decide)
def rev23_s5_ul : FractionPoint := ⟨89389325943747189,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev23_s5_ul_mem : rev23_s5_ul.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane59 rev23_vertex3 rev23_vertex2 rev23_s5_ul
    rev23_vertex3_mem rev23_vertex2_mem (by decide)
def rev23_s5_ur : FractionPoint := ⟨351475835396027,478882946000000,13319330691551,670436124400000⟩
theorem rev23_s5_ur_mem : rev23_s5_ur.real ∈ rationalHull (fractionRow23.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow23 rev23_plane59 rev23_vertex3 rev23_vertex2 rev23_s5_ur
    rev23_vertex3_mem rev23_vertex2_mem (by decide)
theorem rev23_slab5 (p : Point) (hp : p∈IntegerCarrier rev23_planes)
    (hx0 : rev23_s5_ll.real.1≤p.1) (hx1 : p.1≤rev23_s5_lr.real.1) :
    p∈rationalHull (fractionRow23.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev23_plane7 rev23_plane59 rev23_s5_ll rev23_s5_lr rev23_s5_ul rev23_s5_ur
    (by decide) rev23_s5_ll_mem rev23_s5_lr_mem rev23_s5_ul_mem rev23_s5_ur_mem p
    (hp _ rev23_plane7_mem) (hp _ rev23_plane59_mem) hx0 hx1
theorem rev23_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev23_planes) : rev23_s0_ll.real.1≤p.1 := by
  have hc := rev23_plane29.combine_sound rev23_plane68 48252000000 2139440000000 (by decide) (by decide) p
    (hp _ rev23_plane29_mem) (hp _ rev23_plane68_mem)
  exact (rev23_plane29.combine rev23_plane68 48252000000 2139440000000).xBoundCheck_sound rev23_s0_ll.nx rev23_s0_ll.dx true (by decide) p hc
theorem rev23_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev23_planes) : p.1≤rev23_s5_lr.real.1 := by
  have hc := rev23_plane7.combine_sound rev23_plane59 15204000000 287616000000 (by decide) (by decide) p
    (hp _ rev23_plane7_mem) (hp _ rev23_plane59_mem)
  exact (rev23_plane7.combine rev23_plane59 15204000000 287616000000).xBoundCheck_sound rev23_s5_lr.nx rev23_s5_lr.dx false (by decide) p hc
theorem rev23_hull (p : Point) (hp : p∈IntegerCarrier rev23_planes) :
    p∈rationalHull (fractionRow23.map FractionPoint.rational) := by
  have hxlo := rev23_bound0_lo p hp
  have hxhi := rev23_bound0_hi p hp
  by_cases h0 : p.1≤rev23_s0_lr.real.1
  · exact rev23_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev23_s1_lr.real.1
  · exact rev23_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev23_s2_lr.real.1
  · exact rev23_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev23_s3_lr.real.1
  · exact rev23_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p.1≤rev23_s4_lr.real.1
  · exact rev23_slab4 p hp (le_of_lt (lt_of_not_ge h3)) h4
  exact rev23_slab5 p hp (le_of_lt (lt_of_not_ge h4)) hxhi
theorem overlay_in_hull23 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,1,11,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow23 := by
  rw [← fractionRow23_correct]
  exact rev23_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull23
