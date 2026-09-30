import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks12
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev103_planes : List IntegerPlane := integerOverlayPlanes ![7,4,14,13]
def rev103_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev103_plane1_mem : rev103_plane1 ∈ rev103_planes := by decide
def rev103_plane15 : IntegerPlane := ⟨48252000000,2112760000000,1031002749085⟩
theorem rev103_plane15_mem : rev103_plane15 ∈ rev103_planes := by decide
def rev103_plane24 : IntegerPlane := ⟨(-15204000000),(-2139684000000),(-584166228432)⟩
theorem rev103_plane24_mem : rev103_plane24 ∈ rev103_planes := by decide
def rev103_plane54 : IntegerPlane := ⟨(-2139440000000),(-16372000000),(-1762107152575)⟩
theorem rev103_plane54_mem : rev103_plane54 ∈ rev103_planes := by decide
def rev103_plane59 : IntegerPlane := ⟨(-699324000000),(-2145688000000),(-1149963272359)⟩
theorem rev103_plane59_mem : rev103_plane59 ∈ rev103_planes := by decide
def rev103_plane76 : IntegerPlane := ⟨287616000000,(-1855520000000),(-211760240400)⟩
theorem rev103_plane76_mem : rev103_plane76 ∈ rev103_planes := by decide
def rev103_plane78 : IntegerPlane := ⟨746024000000,2083356000000,1711863292059⟩
theorem rev103_plane78_mem : rev103_plane78 ∈ rev103_planes := by decide
def rev103_vertex0 : FractionPoint := fractionRow103[0]!
theorem rev103_vertex0_mem : rev103_vertex0∈fractionRow103 := by decide
def rev103_vertex1 : FractionPoint := fractionRow103[1]!
theorem rev103_vertex1_mem : rev103_vertex1∈fractionRow103 := by decide
def rev103_vertex2 : FractionPoint := fractionRow103[2]!
theorem rev103_vertex2_mem : rev103_vertex2∈fractionRow103 := by decide
def rev103_vertex3 : FractionPoint := fractionRow103[3]!
theorem rev103_vertex3_mem : rev103_vertex3∈fractionRow103 := by decide
def rev103_vertex4 : FractionPoint := fractionRow103[4]!
theorem rev103_vertex4_mem : rev103_vertex4∈fractionRow103 := by decide
def rev103_vertex5 : FractionPoint := fractionRow103[5]!
theorem rev103_vertex5_mem : rev103_vertex5∈fractionRow103 := by decide
def rev103_vertex6 : FractionPoint := fractionRow103[6]!
theorem rev103_vertex6_mem : rev103_vertex6∈fractionRow103 := by decide
def rev103_s0_ll : FractionPoint := ⟨185301496533316869,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev103_s0_ll_mem : rev103_s0_ll.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane54 rev103_vertex3 rev103_vertex4 rev103_s0_ll
    rev103_vertex3_mem rev103_vertex4_mem (by decide)
def rev103_s0_lr : FractionPoint := ⟨940526243324821263,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev103_s0_lr_mem : rev103_s0_lr.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane54 rev103_vertex3 rev103_vertex4 rev103_s0_lr
    rev103_vertex3_mem rev103_vertex4_mem (by decide)
def rev103_s0_ul : FractionPoint := ⟨185301496533316869,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev103_s0_ul_mem : rev103_s0_ul.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane15 rev103_vertex3 rev103_vertex2 rev103_s0_ul
    rev103_vertex3_mem rev103_vertex2_mem (by decide)
def rev103_s0_ur : FractionPoint := ⟨940526243324821263,1144780350548000000,17732647128446386104161,37791345834746757500000⟩
theorem rev103_s0_ur_mem : rev103_s0_ur.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane15 rev103_vertex3 rev103_vertex2 rev103_s0_ur
    rev103_vertex3_mem rev103_vertex2_mem (by decide)
theorem rev103_slab0 (p : Point) (hp : p∈IntegerCarrier rev103_planes)
    (hx0 : rev103_s0_ll.real.1≤p.1) (hx1 : p.1≤rev103_s0_lr.real.1) :
    p∈rationalHull (fractionRow103.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev103_plane54 rev103_plane15 rev103_s0_ll rev103_s0_lr rev103_s0_ul rev103_s0_ur
    (by decide) rev103_s0_ll_mem rev103_s0_lr_mem rev103_s0_ul_mem rev103_s0_ur_mem p
    (hp _ rev103_plane54_mem) (hp _ rev103_plane15_mem) hx0 hx1
def rev103_s1_ll : FractionPoint := ⟨940526243324821263,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev103_s1_ll_mem : rev103_s1_ll.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane59 rev103_vertex4 rev103_vertex5 rev103_s1_ll
    rev103_vertex4_mem rev103_vertex5_mem (by decide)
def rev103_s1_lr : FractionPoint := ⟨20118659135039889,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev103_s1_lr_mem : rev103_s1_lr.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane59 rev103_vertex4 rev103_vertex5 rev103_s1_lr
    rev103_vertex4_mem rev103_vertex5_mem (by decide)
def rev103_s1_ul : FractionPoint := ⟨940526243324821263,1144780350548000000,17732647128446386104161,37791345834746757500000⟩
theorem rev103_s1_ul_mem : rev103_s1_ul.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane15 rev103_vertex3 rev103_vertex2 rev103_s1_ul
    rev103_vertex3_mem rev103_vertex2_mem (by decide)
def rev103_s1_ur : FractionPoint := ⟨20118659135039889,24395155554400000,1511294181272416408981,3221319303069634000000⟩
theorem rev103_s1_ur_mem : rev103_s1_ur.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane15 rev103_vertex3 rev103_vertex2 rev103_s1_ur
    rev103_vertex3_mem rev103_vertex2_mem (by decide)
theorem rev103_slab1 (p : Point) (hp : p∈IntegerCarrier rev103_planes)
    (hx0 : rev103_s1_ll.real.1≤p.1) (hx1 : p.1≤rev103_s1_lr.real.1) :
    p∈rationalHull (fractionRow103.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev103_plane59 rev103_plane15 rev103_s1_ll rev103_s1_lr rev103_s1_ul rev103_s1_ur
    (by decide) rev103_s1_ll_mem rev103_s1_lr_mem rev103_s1_ul_mem rev103_s1_ur_mem p
    (hp _ rev103_plane59_mem) (hp _ rev103_plane15_mem) hx0 hx1
def rev103_s2_ll : FractionPoint := ⟨20118659135039889,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev103_s2_ll_mem : rev103_s2_ll.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane24 rev103_vertex5 rev103_vertex6 rev103_s2_ll
    rev103_vertex5_mem rev103_vertex6_mem (by decide)
def rev103_s2_lr : FractionPoint := ⟨657116793708449,670436124400000,127407110603973,478882946000000⟩
theorem rev103_s2_lr_mem : rev103_s2_lr.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane24 rev103_vertex5 rev103_vertex6 rev103_s2_lr
    rev103_vertex5_mem rev103_vertex6_mem (by decide)
def rev103_s2_ul : FractionPoint := ⟨20118659135039889,24395155554400000,1511294181272416408981,3221319303069634000000⟩
theorem rev103_s2_ul_mem : rev103_s2_ul.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane15 rev103_vertex3 rev103_vertex2 rev103_s2_ul
    rev103_vertex3_mem rev103_vertex2_mem (by decide)
def rev103_s2_ur : FractionPoint := ⟨657116793708449,670436124400000,329757143906136482513,708235313093672000000⟩
theorem rev103_s2_ur_mem : rev103_s2_ur.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane15 rev103_vertex3 rev103_vertex2 rev103_s2_ur
    rev103_vertex3_mem rev103_vertex2_mem (by decide)
theorem rev103_slab2 (p : Point) (hp : p∈IntegerCarrier rev103_planes)
    (hx0 : rev103_s2_ll.real.1≤p.1) (hx1 : p.1≤rev103_s2_lr.real.1) :
    p∈rationalHull (fractionRow103.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev103_plane24 rev103_plane15 rev103_s2_ll rev103_s2_lr rev103_s2_ul rev103_s2_ur
    (by decide) rev103_s2_ll_mem rev103_s2_lr_mem rev103_s2_ul_mem rev103_s2_ur_mem p
    (hp _ rev103_plane24_mem) (hp _ rev103_plane15_mem) hx0 hx1
def rev103_s3_ll : FractionPoint := ⟨657116793708449,670436124400000,127407110603973,478882946000000⟩
theorem rev103_s3_ll_mem : rev103_s3_ll.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane76 rev103_vertex6 rev103_vertex0 rev103_s3_ll
    rev103_vertex6_mem rev103_vertex0_mem (by decide)
def rev103_s3_lr : FractionPoint := ⟨73440526280392179,73782178626400000,574168785778491917841,2139129813825902000000⟩
theorem rev103_s3_lr_mem : rev103_s3_lr.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane76 rev103_vertex6 rev103_vertex0 rev103_s3_lr
    rev103_vertex6_mem rev103_vertex0_mem (by decide)
def rev103_s3_ul : FractionPoint := ⟨657116793708449,670436124400000,329757143906136482513,708235313093672000000⟩
theorem rev103_s3_ul_mem : rev103_s3_ul.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane15 rev103_vertex3 rev103_vertex2 rev103_s3_ul
    rev103_vertex3_mem rev103_vertex2_mem (by decide)
def rev103_s3_ur : FractionPoint := ⟨73440526280392179,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev103_s3_ur_mem : rev103_s3_ur.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane15 rev103_vertex3 rev103_vertex2 rev103_s3_ur
    rev103_vertex3_mem rev103_vertex2_mem (by decide)
theorem rev103_slab3 (p : Point) (hp : p∈IntegerCarrier rev103_planes)
    (hx0 : rev103_s3_ll.real.1≤p.1) (hx1 : p.1≤rev103_s3_lr.real.1) :
    p∈rationalHull (fractionRow103.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev103_plane76 rev103_plane15 rev103_s3_ll rev103_s3_lr rev103_s3_ul rev103_s3_ur
    (by decide) rev103_s3_ll_mem rev103_s3_lr_mem rev103_s3_ul_mem rev103_s3_ur_mem p
    (hp _ rev103_plane76_mem) (hp _ rev103_plane15_mem) hx0 hx1
def rev103_s4_ll : FractionPoint := ⟨73440526280392179,73782178626400000,574168785778491917841,2139129813825902000000⟩
theorem rev103_s4_ll_mem : rev103_s4_ll.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane76 rev103_vertex6 rev103_vertex0 rev103_s4_ll
    rev103_vertex6_mem rev103_vertex0_mem (by decide)
def rev103_s4_lr : FractionPoint := ⟨1,1,1248440601,4638800000⟩
theorem rev103_s4_lr_mem : rev103_s4_lr.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane76 rev103_vertex6 rev103_vertex0 rev103_s4_lr
    rev103_vertex6_mem rev103_vertex0_mem (by decide)
def rev103_s4_ul : FractionPoint := ⟨73440526280392179,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev103_s4_ul_mem : rev103_s4_ul.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane78 rev103_vertex2 rev103_vertex1 rev103_s4_ul
    rev103_vertex2_mem rev103_vertex1_mem (by decide)
def rev103_s4_ur : FractionPoint := ⟨1,1,965839292059,2083356000000⟩
theorem rev103_s4_ur_mem : rev103_s4_ur.real ∈ rationalHull (fractionRow103.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow103 rev103_plane78 rev103_vertex2 rev103_vertex1 rev103_s4_ur
    rev103_vertex2_mem rev103_vertex1_mem (by decide)
theorem rev103_slab4 (p : Point) (hp : p∈IntegerCarrier rev103_planes)
    (hx0 : rev103_s4_ll.real.1≤p.1) (hx1 : p.1≤rev103_s4_lr.real.1) :
    p∈rationalHull (fractionRow103.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev103_plane76 rev103_plane78 rev103_s4_ll rev103_s4_lr rev103_s4_ul rev103_s4_ur
    (by decide) rev103_s4_ll_mem rev103_s4_lr_mem rev103_s4_ul_mem rev103_s4_ur_mem p
    (hp _ rev103_plane76_mem) (hp _ rev103_plane78_mem) hx0 hx1
theorem rev103_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev103_planes) : rev103_s0_ll.real.1≤p.1 := by
  have hc := rev103_plane15.combine_sound rev103_plane54 16372000000 2112760000000 (by decide) (by decide) p
    (hp _ rev103_plane15_mem) (hp _ rev103_plane54_mem)
  exact (rev103_plane15.combine rev103_plane54 16372000000 2112760000000).xBoundCheck_sound rev103_s0_ll.nx rev103_s0_ll.dx true (by decide) p hc
theorem rev103_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev103_planes) : p.1≤rev103_s4_lr.real.1 := by
  have hc := rev103_plane1.combine_sound rev103_plane1 1 0 (by decide) (by decide) p
    (hp _ rev103_plane1_mem) (hp _ rev103_plane1_mem)
  exact (rev103_plane1.combine rev103_plane1 1 0).xBoundCheck_sound rev103_s4_lr.nx rev103_s4_lr.dx false (by decide) p hc
theorem rev103_hull (p : Point) (hp : p∈IntegerCarrier rev103_planes) :
    p∈rationalHull (fractionRow103.map FractionPoint.rational) := by
  have hxlo := rev103_bound0_lo p hp
  have hxhi := rev103_bound0_hi p hp
  by_cases h0 : p.1≤rev103_s0_lr.real.1
  · exact rev103_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev103_s1_lr.real.1
  · exact rev103_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev103_s2_lr.real.1
  · exact rev103_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev103_s3_lr.real.1
  · exact rev103_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev103_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull103 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,4,14,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow103 := by
  rw [← fractionRow103_correct]
  exact rev103_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull103
