import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks5
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev44_planes : List IntegerPlane := integerOverlayPlanes ![4,7,2,1]
def rev44_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev44_plane0_mem : rev44_plane0 ∈ rev44_planes := by decide
def rev44_plane4 : IntegerPlane := ⟨15204000000,(-2139684000000),(-568962228432)⟩
theorem rev44_plane4_mem : rev44_plane4 ∈ rev44_planes := by decide
def rev44_plane35 : IntegerPlane := ⟨(-48252000000),2112760000000,982750749085⟩
theorem rev44_plane35_mem : rev44_plane35 ∈ rev44_planes := by decide
def rev44_plane45 : IntegerPlane := ⟨(-746024000000),2083356000000,965839292059⟩
theorem rev44_plane45_mem : rev44_plane45 ∈ rev44_planes := by decide
def rev44_plane47 : IntegerPlane := ⟨(-287616000000),(-1855520000000),(-499376240400)⟩
theorem rev44_plane47_mem : rev44_plane47 ∈ rev44_planes := by decide
def rev44_plane64 : IntegerPlane := ⟨699324000000,(-2145688000000),(-450639272359)⟩
theorem rev44_plane64_mem : rev44_plane64 ∈ rev44_planes := by decide
def rev44_plane69 : IntegerPlane := ⟨2139440000000,(-16372000000),377332847425⟩
theorem rev44_plane69_mem : rev44_plane69 ∈ rev44_planes := by decide
def rev44_vertex0 : FractionPoint := fractionRow44[0]!
theorem rev44_vertex0_mem : rev44_vertex0∈fractionRow44 := by decide
def rev44_vertex1 : FractionPoint := fractionRow44[1]!
theorem rev44_vertex1_mem : rev44_vertex1∈fractionRow44 := by decide
def rev44_vertex2 : FractionPoint := fractionRow44[2]!
theorem rev44_vertex2_mem : rev44_vertex2∈fractionRow44 := by decide
def rev44_vertex3 : FractionPoint := fractionRow44[3]!
theorem rev44_vertex3_mem : rev44_vertex3∈fractionRow44 := by decide
def rev44_vertex4 : FractionPoint := fractionRow44[4]!
theorem rev44_vertex4_mem : rev44_vertex4∈fractionRow44 := by decide
def rev44_vertex5 : FractionPoint := fractionRow44[5]!
theorem rev44_vertex5_mem : rev44_vertex5∈fractionRow44 := by decide
def rev44_vertex6 : FractionPoint := fractionRow44[6]!
theorem rev44_vertex6_mem : rev44_vertex6∈fractionRow44 := by decide
def rev44_s0_ll : FractionPoint := ⟨0,1,1248440601,4638800000⟩
theorem rev44_s0_ll_mem : rev44_s0_ll.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane47 rev44_vertex1 rev44_vertex2 rev44_s0_ll
    rev44_vertex1_mem rev44_vertex2_mem (by decide)
def rev44_s0_lr : FractionPoint := ⟨341652346007821,73782178626400000,574168785778491917841,2139129813825902000000⟩
theorem rev44_s0_lr_mem : rev44_s0_lr.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane47 rev44_vertex1 rev44_vertex2 rev44_s0_lr
    rev44_vertex1_mem rev44_vertex2_mem (by decide)
def rev44_s0_ul : FractionPoint := ⟨0,1,965839292059,2083356000000⟩
theorem rev44_s0_ul_mem : rev44_s0_ul.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane45 rev44_vertex0 rev44_vertex6 rev44_s0_ul
    rev44_vertex0_mem rev44_vertex6_mem (by decide)
def rev44_s0_ur : FractionPoint := ⟨341652346007821,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev44_s0_ur_mem : rev44_s0_ur.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane45 rev44_vertex0 rev44_vertex6 rev44_s0_ur
    rev44_vertex0_mem rev44_vertex6_mem (by decide)
theorem rev44_slab0 (p : Point) (hp : p∈IntegerCarrier rev44_planes)
    (hx0 : rev44_s0_ll.real.1≤p.1) (hx1 : p.1≤rev44_s0_lr.real.1) :
    p∈rationalHull (fractionRow44.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev44_plane47 rev44_plane45 rev44_s0_ll rev44_s0_lr rev44_s0_ul rev44_s0_ur
    (by decide) rev44_s0_ll_mem rev44_s0_lr_mem rev44_s0_ul_mem rev44_s0_ur_mem p
    (hp _ rev44_plane47_mem) (hp _ rev44_plane45_mem) hx0 hx1
def rev44_s1_ll : FractionPoint := ⟨341652346007821,73782178626400000,574168785778491917841,2139129813825902000000⟩
theorem rev44_s1_ll_mem : rev44_s1_ll.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane47 rev44_vertex1 rev44_vertex2 rev44_s1_ll
    rev44_vertex1_mem rev44_vertex2_mem (by decide)
def rev44_s1_lr : FractionPoint := ⟨13319330691551,670436124400000,127407110603973,478882946000000⟩
theorem rev44_s1_lr_mem : rev44_s1_lr.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane47 rev44_vertex1 rev44_vertex2 rev44_s1_lr
    rev44_vertex1_mem rev44_vertex2_mem (by decide)
def rev44_s1_ul : FractionPoint := ⟨341652346007821,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev44_s1_ul_mem : rev44_s1_ul.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane35 rev44_vertex6 rev44_vertex5 rev44_s1_ul
    rev44_vertex6_mem rev44_vertex5_mem (by decide)
def rev44_s1_ur : FractionPoint := ⟨13319330691551,670436124400000,329757143906136482513,708235313093672000000⟩
theorem rev44_s1_ur_mem : rev44_s1_ur.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane35 rev44_vertex6 rev44_vertex5 rev44_s1_ur
    rev44_vertex6_mem rev44_vertex5_mem (by decide)
theorem rev44_slab1 (p : Point) (hp : p∈IntegerCarrier rev44_planes)
    (hx0 : rev44_s1_ll.real.1≤p.1) (hx1 : p.1≤rev44_s1_lr.real.1) :
    p∈rationalHull (fractionRow44.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev44_plane47 rev44_plane35 rev44_s1_ll rev44_s1_lr rev44_s1_ul rev44_s1_ur
    (by decide) rev44_s1_ll_mem rev44_s1_lr_mem rev44_s1_ul_mem rev44_s1_ur_mem p
    (hp _ rev44_plane47_mem) (hp _ rev44_plane35_mem) hx0 hx1
def rev44_s2_ll : FractionPoint := ⟨13319330691551,670436124400000,127407110603973,478882946000000⟩
theorem rev44_s2_ll_mem : rev44_s2_ll.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane4 rev44_vertex2 rev44_vertex3 rev44_s2_ll
    rev44_vertex2_mem rev44_vertex3_mem (by decide)
def rev44_s2_lr : FractionPoint := ⟨4276496419360111,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev44_s2_lr_mem : rev44_s2_lr.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane4 rev44_vertex2 rev44_vertex3 rev44_s2_lr
    rev44_vertex2_mem rev44_vertex3_mem (by decide)
def rev44_s2_ul : FractionPoint := ⟨13319330691551,670436124400000,329757143906136482513,708235313093672000000⟩
theorem rev44_s2_ul_mem : rev44_s2_ul.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane35 rev44_vertex6 rev44_vertex5 rev44_s2_ul
    rev44_vertex6_mem rev44_vertex5_mem (by decide)
def rev44_s2_ur : FractionPoint := ⟨4276496419360111,24395155554400000,1511294181272416408981,3221319303069634000000⟩
theorem rev44_s2_ur_mem : rev44_s2_ur.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane35 rev44_vertex6 rev44_vertex5 rev44_s2_ur
    rev44_vertex6_mem rev44_vertex5_mem (by decide)
theorem rev44_slab2 (p : Point) (hp : p∈IntegerCarrier rev44_planes)
    (hx0 : rev44_s2_ll.real.1≤p.1) (hx1 : p.1≤rev44_s2_lr.real.1) :
    p∈rationalHull (fractionRow44.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev44_plane4 rev44_plane35 rev44_s2_ll rev44_s2_lr rev44_s2_ul rev44_s2_ur
    (by decide) rev44_s2_ll_mem rev44_s2_lr_mem rev44_s2_ul_mem rev44_s2_ur_mem p
    (hp _ rev44_plane4_mem) (hp _ rev44_plane35_mem) hx0 hx1
def rev44_s3_ll : FractionPoint := ⟨4276496419360111,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev44_s3_ll_mem : rev44_s3_ll.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane64 rev44_vertex3 rev44_vertex4 rev44_s3_ll
    rev44_vertex3_mem rev44_vertex4_mem (by decide)
def rev44_s3_lr : FractionPoint := ⟨204254107223178737,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev44_s3_lr_mem : rev44_s3_lr.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane64 rev44_vertex3 rev44_vertex4 rev44_s3_lr
    rev44_vertex3_mem rev44_vertex4_mem (by decide)
def rev44_s3_ul : FractionPoint := ⟨4276496419360111,24395155554400000,1511294181272416408981,3221319303069634000000⟩
theorem rev44_s3_ul_mem : rev44_s3_ul.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane35 rev44_vertex6 rev44_vertex5 rev44_s3_ul
    rev44_vertex6_mem rev44_vertex5_mem (by decide)
def rev44_s3_ur : FractionPoint := ⟨204254107223178737,1144780350548000000,17732647128446386104161,37791345834746757500000⟩
theorem rev44_s3_ur_mem : rev44_s3_ur.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane35 rev44_vertex6 rev44_vertex5 rev44_s3_ur
    rev44_vertex6_mem rev44_vertex5_mem (by decide)
theorem rev44_slab3 (p : Point) (hp : p∈IntegerCarrier rev44_planes)
    (hx0 : rev44_s3_ll.real.1≤p.1) (hx1 : p.1≤rev44_s3_lr.real.1) :
    p∈rationalHull (fractionRow44.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev44_plane64 rev44_plane35 rev44_s3_ll rev44_s3_lr rev44_s3_ul rev44_s3_ur
    (by decide) rev44_s3_ll_mem rev44_s3_lr_mem rev44_s3_ul_mem rev44_s3_ur_mem p
    (hp _ rev44_plane64_mem) (hp _ rev44_plane35_mem) hx0 hx1
def rev44_s4_ll : FractionPoint := ⟨204254107223178737,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev44_s4_ll_mem : rev44_s4_ll.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane69 rev44_vertex4 rev44_vertex5 rev44_s4_ll
    rev44_vertex4_mem rev44_vertex5_mem (by decide)
def rev44_s4_lr : FractionPoint := ⟨40665167099483131,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev44_s4_lr_mem : rev44_s4_lr.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane69 rev44_vertex4 rev44_vertex5 rev44_s4_lr
    rev44_vertex4_mem rev44_vertex5_mem (by decide)
def rev44_s4_ul : FractionPoint := ⟨204254107223178737,1144780350548000000,17732647128446386104161,37791345834746757500000⟩
theorem rev44_s4_ul_mem : rev44_s4_ul.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane35 rev44_vertex6 rev44_vertex5 rev44_s4_ul
    rev44_vertex6_mem rev44_vertex5_mem (by decide)
def rev44_s4_ur : FractionPoint := ⟨40665167099483131,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev44_s4_ur_mem : rev44_s4_ur.real ∈ rationalHull (fractionRow44.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow44 rev44_plane35 rev44_vertex6 rev44_vertex5 rev44_s4_ur
    rev44_vertex6_mem rev44_vertex5_mem (by decide)
theorem rev44_slab4 (p : Point) (hp : p∈IntegerCarrier rev44_planes)
    (hx0 : rev44_s4_ll.real.1≤p.1) (hx1 : p.1≤rev44_s4_lr.real.1) :
    p∈rationalHull (fractionRow44.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev44_plane69 rev44_plane35 rev44_s4_ll rev44_s4_lr rev44_s4_ul rev44_s4_ur
    (by decide) rev44_s4_ll_mem rev44_s4_lr_mem rev44_s4_ul_mem rev44_s4_ur_mem p
    (hp _ rev44_plane69_mem) (hp _ rev44_plane35_mem) hx0 hx1
theorem rev44_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev44_planes) : rev44_s0_ll.real.1≤p.1 := by
  have hc := rev44_plane0.combine_sound rev44_plane0 1 0 (by decide) (by decide) p
    (hp _ rev44_plane0_mem) (hp _ rev44_plane0_mem)
  exact (rev44_plane0.combine rev44_plane0 1 0).xBoundCheck_sound rev44_s0_ll.nx rev44_s0_ll.dx true (by decide) p hc
theorem rev44_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev44_planes) : p.1≤rev44_s4_lr.real.1 := by
  have hc := rev44_plane35.combine_sound rev44_plane69 16372000000 2112760000000 (by decide) (by decide) p
    (hp _ rev44_plane35_mem) (hp _ rev44_plane69_mem)
  exact (rev44_plane35.combine rev44_plane69 16372000000 2112760000000).xBoundCheck_sound rev44_s4_lr.nx rev44_s4_lr.dx false (by decide) p hc
theorem rev44_hull (p : Point) (hp : p∈IntegerCarrier rev44_planes) :
    p∈rationalHull (fractionRow44.map FractionPoint.rational) := by
  have hxlo := rev44_bound0_lo p hp
  have hxhi := rev44_bound0_hi p hp
  by_cases h0 : p.1≤rev44_s0_lr.real.1
  · exact rev44_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev44_s1_lr.real.1
  · exact rev44_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev44_s2_lr.real.1
  · exact rev44_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev44_s3_lr.real.1
  · exact rev44_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev44_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull44 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,7,2,1] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow44 := by
  rw [← fractionRow44_correct]
  exact rev44_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull44
