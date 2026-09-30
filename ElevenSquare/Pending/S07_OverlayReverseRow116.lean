import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks14
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev116_planes : List IntegerPlane := integerOverlayPlanes ![8,11,1,2]
def rev116_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev116_plane0_mem : rev116_plane0 ∈ rev116_planes := by decide
def rev116_plane8 : IntegerPlane := ⟨(-48252000000),(-2112760000000),(-1130009250915)⟩
theorem rev116_plane8_mem : rev116_plane8 ∈ rev116_planes := by decide
def rev116_plane39 : IntegerPlane := ⟨15204000000,2139684000000,1570721771568⟩
theorem rev116_plane39_mem : rev116_plane39 ∈ rev116_planes := by decide
def rev116_plane44 : IntegerPlane := ⟨699324000000,2145688000000,1695048727641⟩
theorem rev116_plane44_mem : rev116_plane44 ∈ rev116_planes := by decide
def rev116_plane49 : IntegerPlane := ⟨2139440000000,16372000000,393704847425⟩
theorem rev116_plane49_mem : rev116_plane49 ∈ rev116_planes := by decide
def rev116_plane65 : IntegerPlane := ⟨(-746024000000),(-2083356000000),(-1117516707941)⟩
theorem rev116_plane65_mem : rev116_plane65 ∈ rev116_planes := by decide
def rev116_plane67 : IntegerPlane := ⟨(-287616000000),1855520000000,1356143759600⟩
theorem rev116_plane67_mem : rev116_plane67 ∈ rev116_planes := by decide
def rev116_vertex0 : FractionPoint := fractionRow116[0]!
theorem rev116_vertex0_mem : rev116_vertex0∈fractionRow116 := by decide
def rev116_vertex1 : FractionPoint := fractionRow116[1]!
theorem rev116_vertex1_mem : rev116_vertex1∈fractionRow116 := by decide
def rev116_vertex2 : FractionPoint := fractionRow116[2]!
theorem rev116_vertex2_mem : rev116_vertex2∈fractionRow116 := by decide
def rev116_vertex3 : FractionPoint := fractionRow116[3]!
theorem rev116_vertex3_mem : rev116_vertex3∈fractionRow116 := by decide
def rev116_vertex4 : FractionPoint := fractionRow116[4]!
theorem rev116_vertex4_mem : rev116_vertex4∈fractionRow116 := by decide
def rev116_vertex5 : FractionPoint := fractionRow116[5]!
theorem rev116_vertex5_mem : rev116_vertex5∈fractionRow116 := by decide
def rev116_vertex6 : FractionPoint := fractionRow116[6]!
theorem rev116_vertex6_mem : rev116_vertex6∈fractionRow116 := by decide
def rev116_s0_ll : FractionPoint := ⟨0,1,1117516707941,2083356000000⟩
theorem rev116_s0_ll_mem : rev116_s0_ll.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane65 rev116_vertex1 rev116_vertex2 rev116_s0_ll
    rev116_vertex1_mem rev116_vertex2_mem (by decide)
def rev116_s0_lr : FractionPoint := ⟨341652346007821,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev116_s0_lr_mem : rev116_s0_lr.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane65 rev116_vertex1 rev116_vertex2 rev116_s0_lr
    rev116_vertex1_mem rev116_vertex2_mem (by decide)
def rev116_s0_ul : FractionPoint := ⟨0,1,3390359399,4638800000⟩
theorem rev116_s0_ul_mem : rev116_s0_ul.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane67 rev116_vertex0 rev116_vertex6 rev116_s0_ul
    rev116_vertex0_mem rev116_vertex6_mem (by decide)
def rev116_s0_ur : FractionPoint := ⟨341652346007821,73782178626400000,1564961028047410082159,2139129813825902000000⟩
theorem rev116_s0_ur_mem : rev116_s0_ur.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane67 rev116_vertex0 rev116_vertex6 rev116_s0_ur
    rev116_vertex0_mem rev116_vertex6_mem (by decide)
theorem rev116_slab0 (p : Point) (hp : p∈IntegerCarrier rev116_planes)
    (hx0 : rev116_s0_ll.real.1≤p.1) (hx1 : p.1≤rev116_s0_lr.real.1) :
    p∈rationalHull (fractionRow116.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev116_plane65 rev116_plane67 rev116_s0_ll rev116_s0_lr rev116_s0_ul rev116_s0_ur
    (by decide) rev116_s0_ll_mem rev116_s0_lr_mem rev116_s0_ul_mem rev116_s0_ur_mem p
    (hp _ rev116_plane65_mem) (hp _ rev116_plane67_mem) hx0 hx1
def rev116_s1_ll : FractionPoint := ⟨341652346007821,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev116_s1_ll_mem : rev116_s1_ll.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane8 rev116_vertex2 rev116_vertex3 rev116_s1_ll
    rev116_vertex2_mem rev116_vertex3_mem (by decide)
def rev116_s1_lr : FractionPoint := ⟨13319330691551,670436124400000,378478169187535517487,708235313093672000000⟩
theorem rev116_s1_lr_mem : rev116_s1_lr.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane8 rev116_vertex2 rev116_vertex3 rev116_s1_lr
    rev116_vertex2_mem rev116_vertex3_mem (by decide)
def rev116_s1_ul : FractionPoint := ⟨341652346007821,73782178626400000,1564961028047410082159,2139129813825902000000⟩
theorem rev116_s1_ul_mem : rev116_s1_ul.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane67 rev116_vertex0 rev116_vertex6 rev116_s1_ul
    rev116_vertex0_mem rev116_vertex6_mem (by decide)
def rev116_s1_ur : FractionPoint := ⟨13319330691551,670436124400000,351475835396027,478882946000000⟩
theorem rev116_s1_ur_mem : rev116_s1_ur.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane67 rev116_vertex0 rev116_vertex6 rev116_s1_ur
    rev116_vertex0_mem rev116_vertex6_mem (by decide)
theorem rev116_slab1 (p : Point) (hp : p∈IntegerCarrier rev116_planes)
    (hx0 : rev116_s1_ll.real.1≤p.1) (hx1 : p.1≤rev116_s1_lr.real.1) :
    p∈rationalHull (fractionRow116.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev116_plane8 rev116_plane67 rev116_s1_ll rev116_s1_lr rev116_s1_ul rev116_s1_ur
    (by decide) rev116_s1_ll_mem rev116_s1_lr_mem rev116_s1_ul_mem rev116_s1_ur_mem p
    (hp _ rev116_plane8_mem) (hp _ rev116_plane67_mem) hx0 hx1
def rev116_s2_ll : FractionPoint := ⟨13319330691551,670436124400000,378478169187535517487,708235313093672000000⟩
theorem rev116_s2_ll_mem : rev116_s2_ll.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane8 rev116_vertex2 rev116_vertex3 rev116_s2_ll
    rev116_vertex2_mem rev116_vertex3_mem (by decide)
def rev116_s2_lr : FractionPoint := ⟨4276496419360111,24395155554400000,1710025121797217591019,3221319303069634000000⟩
theorem rev116_s2_lr_mem : rev116_s2_lr.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane8 rev116_vertex2 rev116_vertex3 rev116_s2_lr
    rev116_vertex2_mem rev116_vertex3_mem (by decide)
def rev116_s2_ul : FractionPoint := ⟨13319330691551,670436124400000,351475835396027,478882946000000⟩
theorem rev116_s2_ul_mem : rev116_s2_ul.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane39 rev116_vertex6 rev116_vertex5 rev116_s2_ul
    rev116_vertex6_mem rev116_vertex5_mem (by decide)
def rev116_s2_ur : FractionPoint := ⟨4276496419360111,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev116_s2_ur_mem : rev116_s2_ur.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane39 rev116_vertex6 rev116_vertex5 rev116_s2_ur
    rev116_vertex6_mem rev116_vertex5_mem (by decide)
theorem rev116_slab2 (p : Point) (hp : p∈IntegerCarrier rev116_planes)
    (hx0 : rev116_s2_ll.real.1≤p.1) (hx1 : p.1≤rev116_s2_lr.real.1) :
    p∈rationalHull (fractionRow116.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev116_plane8 rev116_plane39 rev116_s2_ll rev116_s2_lr rev116_s2_ul rev116_s2_ur
    (by decide) rev116_s2_ll_mem rev116_s2_lr_mem rev116_s2_ul_mem rev116_s2_ur_mem p
    (hp _ rev116_plane8_mem) (hp _ rev116_plane39_mem) hx0 hx1
def rev116_s3_ll : FractionPoint := ⟨4276496419360111,24395155554400000,1710025121797217591019,3221319303069634000000⟩
theorem rev116_s3_ll_mem : rev116_s3_ll.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane8 rev116_vertex2 rev116_vertex3 rev116_s3_ll
    rev116_vertex2_mem rev116_vertex3_mem (by decide)
def rev116_s3_lr : FractionPoint := ⟨204254107223178737,1144780350548000000,20058698706300371395839,37791345834746757500000⟩
theorem rev116_s3_lr_mem : rev116_s3_lr.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane8 rev116_vertex2 rev116_vertex3 rev116_s3_lr
    rev116_vertex2_mem rev116_vertex3_mem (by decide)
def rev116_s3_ul : FractionPoint := ⟨4276496419360111,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev116_s3_ul_mem : rev116_s3_ul.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane44 rev116_vertex5 rev116_vertex4 rev116_s3_ul
    rev116_vertex5_mem rev116_vertex4_mem (by decide)
def rev116_s3_ur : FractionPoint := ⟨204254107223178737,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev116_s3_ur_mem : rev116_s3_ur.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane44 rev116_vertex5 rev116_vertex4 rev116_s3_ur
    rev116_vertex5_mem rev116_vertex4_mem (by decide)
theorem rev116_slab3 (p : Point) (hp : p∈IntegerCarrier rev116_planes)
    (hx0 : rev116_s3_ll.real.1≤p.1) (hx1 : p.1≤rev116_s3_lr.real.1) :
    p∈rationalHull (fractionRow116.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev116_plane8 rev116_plane44 rev116_s3_ll rev116_s3_lr rev116_s3_ul rev116_s3_ur
    (by decide) rev116_s3_ll_mem rev116_s3_lr_mem rev116_s3_ul_mem rev116_s3_ur_mem p
    (hp _ rev116_plane8_mem) (hp _ rev116_plane44_mem) hx0 hx1
def rev116_s4_ll : FractionPoint := ⟨204254107223178737,1144780350548000000,20058698706300371395839,37791345834746757500000⟩
theorem rev116_s4_ll_mem : rev116_s4_ll.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane8 rev116_vertex2 rev116_vertex3 rev116_s4_ll
    rev116_vertex2_mem rev116_vertex3_mem (by decide)
def rev116_s4_lr : FractionPoint := ⟨40665167099483131,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev116_s4_lr_mem : rev116_s4_lr.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane8 rev116_vertex2 rev116_vertex3 rev116_s4_lr
    rev116_vertex2_mem rev116_vertex3_mem (by decide)
def rev116_s4_ul : FractionPoint := ⟨204254107223178737,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev116_s4_ul_mem : rev116_s4_ul.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane49 rev116_vertex4 rev116_vertex3 rev116_s4_ul
    rev116_vertex4_mem rev116_vertex3_mem (by decide)
def rev116_s4_ur : FractionPoint := ⟨40665167099483131,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev116_s4_ur_mem : rev116_s4_ur.real ∈ rationalHull (fractionRow116.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow116 rev116_plane49 rev116_vertex4 rev116_vertex3 rev116_s4_ur
    rev116_vertex4_mem rev116_vertex3_mem (by decide)
theorem rev116_slab4 (p : Point) (hp : p∈IntegerCarrier rev116_planes)
    (hx0 : rev116_s4_ll.real.1≤p.1) (hx1 : p.1≤rev116_s4_lr.real.1) :
    p∈rationalHull (fractionRow116.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev116_plane8 rev116_plane49 rev116_s4_ll rev116_s4_lr rev116_s4_ul rev116_s4_ur
    (by decide) rev116_s4_ll_mem rev116_s4_lr_mem rev116_s4_ul_mem rev116_s4_ur_mem p
    (hp _ rev116_plane8_mem) (hp _ rev116_plane49_mem) hx0 hx1
theorem rev116_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev116_planes) : rev116_s0_ll.real.1≤p.1 := by
  have hc := rev116_plane0.combine_sound rev116_plane0 1 0 (by decide) (by decide) p
    (hp _ rev116_plane0_mem) (hp _ rev116_plane0_mem)
  exact (rev116_plane0.combine rev116_plane0 1 0).xBoundCheck_sound rev116_s0_ll.nx rev116_s0_ll.dx true (by decide) p hc
theorem rev116_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev116_planes) : p.1≤rev116_s4_lr.real.1 := by
  have hc := rev116_plane8.combine_sound rev116_plane49 16372000000 2112760000000 (by decide) (by decide) p
    (hp _ rev116_plane8_mem) (hp _ rev116_plane49_mem)
  exact (rev116_plane8.combine rev116_plane49 16372000000 2112760000000).xBoundCheck_sound rev116_s4_lr.nx rev116_s4_lr.dx false (by decide) p hc
theorem rev116_hull (p : Point) (hp : p∈IntegerCarrier rev116_planes) :
    p∈rationalHull (fractionRow116.map FractionPoint.rational) := by
  have hxlo := rev116_bound0_lo p hp
  have hxhi := rev116_bound0_hi p hp
  by_cases h0 : p.1≤rev116_s0_lr.real.1
  · exact rev116_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev116_s1_lr.real.1
  · exact rev116_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev116_s2_lr.real.1
  · exact rev116_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev116_s3_lr.real.1
  · exact rev116_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev116_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull116 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,11,1,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow116 := by
  rw [← fractionRow116_correct]
  exact rev116_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull116
