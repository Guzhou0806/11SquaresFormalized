import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks2
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev16_planes : List IntegerPlane := integerOverlayPlanes ![1,2,7,4]
def rev16_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev16_plane2_mem : rev16_plane2 ∈ rev16_planes := by decide
def rev16_plane4 : IntegerPlane := ⟨(-2145688000000),699324000000,(-450639272359)⟩
theorem rev16_plane4_mem : rev16_plane4 ∈ rev16_planes := by decide
def rev16_plane9 : IntegerPlane := ⟨(-16372000000),2139440000000,377332847425⟩
theorem rev16_plane9_mem : rev16_plane9 ∈ rev16_planes := by decide
def rev16_plane25 : IntegerPlane := ⟨2083356000000,(-746024000000),965839292059⟩
theorem rev16_plane25_mem : rev16_plane25 ∈ rev16_planes := by decide
def rev16_plane27 : IntegerPlane := ⟨(-1855520000000),(-287616000000),(-499376240400)⟩
theorem rev16_plane27_mem : rev16_plane27 ∈ rev16_planes := by decide
def rev16_plane55 : IntegerPlane := ⟨2112760000000,(-48252000000),982750749085⟩
theorem rev16_plane55_mem : rev16_plane55 ∈ rev16_planes := by decide
def rev16_plane64 : IntegerPlane := ⟨(-2139684000000),15204000000,(-568962228432)⟩
theorem rev16_plane64_mem : rev16_plane64 ∈ rev16_planes := by decide
def rev16_vertex0 : FractionPoint := fractionRow16[0]!
theorem rev16_vertex0_mem : rev16_vertex0∈fractionRow16 := by decide
def rev16_vertex1 : FractionPoint := fractionRow16[1]!
theorem rev16_vertex1_mem : rev16_vertex1∈fractionRow16 := by decide
def rev16_vertex2 : FractionPoint := fractionRow16[2]!
theorem rev16_vertex2_mem : rev16_vertex2∈fractionRow16 := by decide
def rev16_vertex3 : FractionPoint := fractionRow16[3]!
theorem rev16_vertex3_mem : rev16_vertex3∈fractionRow16 := by decide
def rev16_vertex4 : FractionPoint := fractionRow16[4]!
theorem rev16_vertex4_mem : rev16_vertex4∈fractionRow16 := by decide
def rev16_vertex5 : FractionPoint := fractionRow16[5]!
theorem rev16_vertex5_mem : rev16_vertex5∈fractionRow16 := by decide
def rev16_vertex6 : FractionPoint := fractionRow16[6]!
theorem rev16_vertex6_mem : rev16_vertex6∈fractionRow16 := by decide
def rev16_s0_ll : FractionPoint := ⟨127407110603973,478882946000000,13319330691551,670436124400000⟩
theorem rev16_s0_ll_mem : rev16_s0_ll.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane27 rev16_vertex6 rev16_vertex0 rev16_s0_ll
    rev16_vertex6_mem rev16_vertex0_mem (by decide)
def rev16_s0_lr : FractionPoint := ⟨32586451828252811,121975777772000000,2793701420547453263,219263658122947200000⟩
theorem rev16_s0_lr_mem : rev16_s0_lr.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane27 rev16_vertex6 rev16_vertex0 rev16_s0_lr
    rev16_vertex6_mem rev16_vertex0_mem (by decide)
def rev16_s0_ul : FractionPoint := ⟨127407110603973,478882946000000,13319330691551,670436124400000⟩
theorem rev16_s0_ul_mem : rev16_s0_ul.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane64 rev16_vertex6 rev16_vertex5 rev16_s0_ul
    rev16_vertex6_mem rev16_vertex5_mem (by decide)
def rev16_s0_ur : FractionPoint := ⟨32586451828252811,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev16_s0_ur_mem : rev16_s0_ur.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane64 rev16_vertex6 rev16_vertex5 rev16_s0_ur
    rev16_vertex6_mem rev16_vertex5_mem (by decide)
theorem rev16_slab0 (p : Point) (hp : p∈IntegerCarrier rev16_planes)
    (hx0 : rev16_s0_ll.real.1≤p.1) (hx1 : p.1≤rev16_s0_lr.real.1) :
    p∈rationalHull (fractionRow16.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev16_plane27 rev16_plane64 rev16_s0_ll rev16_s0_lr rev16_s0_ul rev16_s0_ur
    (by decide) rev16_s0_ll_mem rev16_s0_lr_mem rev16_s0_ul_mem rev16_s0_ur_mem p
    (hp _ rev16_plane27_mem) (hp _ rev16_plane64_mem) hx0 hx1
def rev16_s1_ll : FractionPoint := ⟨32586451828252811,121975777772000000,2793701420547453263,219263658122947200000⟩
theorem rev16_s1_ll_mem : rev16_s1_ll.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane27 rev16_vertex6 rev16_vertex0 rev16_s1_ll
    rev16_vertex6_mem rev16_vertex0_mem (by decide)
def rev16_s1_lr : FractionPoint := ⟨61399680052418983,228956070109600000,2543044857664953823,411571431629016960000⟩
theorem rev16_s1_lr_mem : rev16_s1_lr.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane27 rev16_vertex6 rev16_vertex0 rev16_s1_lr
    rev16_vertex6_mem rev16_vertex0_mem (by decide)
def rev16_s1_ul : FractionPoint := ⟨32586451828252811,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev16_s1_ul_mem : rev16_s1_ul.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane4 rev16_vertex5 rev16_vertex4 rev16_s1_ul
    rev16_vertex5_mem rev16_vertex4_mem (by decide)
def rev16_s1_ur : FractionPoint := ⟨61399680052418983,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev16_s1_ur_mem : rev16_s1_ur.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane4 rev16_vertex5 rev16_vertex4 rev16_s1_ur
    rev16_vertex5_mem rev16_vertex4_mem (by decide)
theorem rev16_slab1 (p : Point) (hp : p∈IntegerCarrier rev16_planes)
    (hx0 : rev16_s1_ll.real.1≤p.1) (hx1 : p.1≤rev16_s1_lr.real.1) :
    p∈rationalHull (fractionRow16.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev16_plane27 rev16_plane4 rev16_s1_ll rev16_s1_lr rev16_s1_ul rev16_s1_ur
    (by decide) rev16_s1_ll_mem rev16_s1_lr_mem rev16_s1_ul_mem rev16_s1_ur_mem p
    (hp _ rev16_plane27_mem) (hp _ rev16_plane4_mem) hx0 hx1
def rev16_s2_ll : FractionPoint := ⟨61399680052418983,228956070109600000,2543044857664953823,411571431629016960000⟩
theorem rev16_s2_ll_mem : rev16_s2_ll.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane27 rev16_vertex6 rev16_vertex0 rev16_s2_ll
    rev16_vertex6_mem rev16_vertex0_mem (by decide)
def rev16_s2_lr : FractionPoint := ⟨1248440601,4638800000,0,1⟩
theorem rev16_s2_lr_mem : rev16_s2_lr.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane27 rev16_vertex6 rev16_vertex0 rev16_s2_lr
    rev16_vertex6_mem rev16_vertex0_mem (by decide)
def rev16_s2_ul : FractionPoint := ⟨61399680052418983,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev16_s2_ul_mem : rev16_s2_ul.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane9 rev16_vertex4 rev16_vertex3 rev16_s2_ul
    rev16_vertex4_mem rev16_vertex3_mem (by decide)
def rev16_s2_ur : FractionPoint := ⟨1248440601,4638800000,885405541077331,4962217136000000⟩
theorem rev16_s2_ur_mem : rev16_s2_ur.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane9 rev16_vertex4 rev16_vertex3 rev16_s2_ur
    rev16_vertex4_mem rev16_vertex3_mem (by decide)
theorem rev16_slab2 (p : Point) (hp : p∈IntegerCarrier rev16_planes)
    (hx0 : rev16_s2_ll.real.1≤p.1) (hx1 : p.1≤rev16_s2_lr.real.1) :
    p∈rationalHull (fractionRow16.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev16_plane27 rev16_plane9 rev16_s2_ll rev16_s2_lr rev16_s2_ul rev16_s2_ur
    (by decide) rev16_s2_ll_mem rev16_s2_lr_mem rev16_s2_ul_mem rev16_s2_ur_mem p
    (hp _ rev16_plane27_mem) (hp _ rev16_plane9_mem) hx0 hx1
def rev16_s3_ll : FractionPoint := ⟨1248440601,4638800000,0,1⟩
theorem rev16_s3_ll_mem : rev16_s3_ll.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane2 rev16_vertex0 rev16_vertex1 rev16_s3_ll
    rev16_vertex0_mem rev16_vertex1_mem (by decide)
def rev16_s3_lr : FractionPoint := ⟨965839292059,2083356000000,0,1⟩
theorem rev16_s3_lr_mem : rev16_s3_lr.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane2 rev16_vertex0 rev16_vertex1 rev16_s3_lr
    rev16_vertex0_mem rev16_vertex1_mem (by decide)
def rev16_s3_ul : FractionPoint := ⟨1248440601,4638800000,885405541077331,4962217136000000⟩
theorem rev16_s3_ul_mem : rev16_s3_ul.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane9 rev16_vertex4 rev16_vertex3 rev16_s3_ul
    rev16_vertex4_mem rev16_vertex3_mem (by decide)
def rev16_s3_ur : FractionPoint := ⟨965839292059,2083356000000,100241421571193531,557151895080000000⟩
theorem rev16_s3_ur_mem : rev16_s3_ur.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane9 rev16_vertex4 rev16_vertex3 rev16_s3_ur
    rev16_vertex4_mem rev16_vertex3_mem (by decide)
theorem rev16_slab3 (p : Point) (hp : p∈IntegerCarrier rev16_planes)
    (hx0 : rev16_s3_ll.real.1≤p.1) (hx1 : p.1≤rev16_s3_lr.real.1) :
    p∈rationalHull (fractionRow16.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev16_plane2 rev16_plane9 rev16_s3_ll rev16_s3_lr rev16_s3_ul rev16_s3_ur
    (by decide) rev16_s3_ll_mem rev16_s3_lr_mem rev16_s3_ul_mem rev16_s3_ur_mem p
    (hp _ rev16_plane2_mem) (hp _ rev16_plane9_mem) hx0 hx1
def rev16_s4_ll : FractionPoint := ⟨965839292059,2083356000000,0,1⟩
theorem rev16_s4_ll_mem : rev16_s4_ll.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane25 rev16_vertex1 rev16_vertex2 rev16_s4_ll
    rev16_vertex1_mem rev16_vertex2_mem (by decide)
def rev16_s4_lr : FractionPoint := ⟨171637991828739293,368910893132000000,341652346007821,73782178626400000⟩
theorem rev16_s4_lr_mem : rev16_s4_lr.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane25 rev16_vertex1 rev16_vertex2 rev16_s4_lr
    rev16_vertex1_mem rev16_vertex2_mem (by decide)
def rev16_s4_ul : FractionPoint := ⟨965839292059,2083356000000,100241421571193531,557151895080000000⟩
theorem rev16_s4_ul_mem : rev16_s4_ul.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane9 rev16_vertex4 rev16_vertex3 rev16_s4_ul
    rev16_vertex4_mem rev16_vertex3_mem (by decide)
def rev16_s4_ur : FractionPoint := ⟨171637991828739293,368910893132000000,8875765934613597255631,49328920075145380000000⟩
theorem rev16_s4_ur_mem : rev16_s4_ur.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane9 rev16_vertex4 rev16_vertex3 rev16_s4_ur
    rev16_vertex4_mem rev16_vertex3_mem (by decide)
theorem rev16_slab4 (p : Point) (hp : p∈IntegerCarrier rev16_planes)
    (hx0 : rev16_s4_ll.real.1≤p.1) (hx1 : p.1≤rev16_s4_lr.real.1) :
    p∈rationalHull (fractionRow16.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev16_plane25 rev16_plane9 rev16_s4_ll rev16_s4_lr rev16_s4_ul rev16_s4_ur
    (by decide) rev16_s4_ll_mem rev16_s4_lr_mem rev16_s4_ul_mem rev16_s4_ur_mem p
    (hp _ rev16_plane25_mem) (hp _ rev16_plane9_mem) hx0 hx1
def rev16_s5_ll : FractionPoint := ⟨171637991828739293,368910893132000000,341652346007821,73782178626400000⟩
theorem rev16_s5_ll_mem : rev16_s5_ll.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane55 rev16_vertex2 rev16_vertex3 rev16_s5_ll
    rev16_vertex2_mem rev16_vertex3_mem (by decide)
def rev16_s5_lr : FractionPoint := ⟨4241486654352727,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev16_s5_lr_mem : rev16_s5_lr.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane55 rev16_vertex2 rev16_vertex3 rev16_s5_lr
    rev16_vertex2_mem rev16_vertex3_mem (by decide)
def rev16_s5_ul : FractionPoint := ⟨171637991828739293,368910893132000000,8875765934613597255631,49328920075145380000000⟩
theorem rev16_s5_ul_mem : rev16_s5_ul.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane9 rev16_vertex4 rev16_vertex3 rev16_s5_ul
    rev16_vertex4_mem rev16_vertex3_mem (by decide)
def rev16_s5_ur : FractionPoint := ⟨4241486654352727,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev16_s5_ur_mem : rev16_s5_ur.real ∈ rationalHull (fractionRow16.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow16 rev16_plane9 rev16_vertex4 rev16_vertex3 rev16_s5_ur
    rev16_vertex4_mem rev16_vertex3_mem (by decide)
theorem rev16_slab5 (p : Point) (hp : p∈IntegerCarrier rev16_planes)
    (hx0 : rev16_s5_ll.real.1≤p.1) (hx1 : p.1≤rev16_s5_lr.real.1) :
    p∈rationalHull (fractionRow16.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev16_plane55 rev16_plane9 rev16_s5_ll rev16_s5_lr rev16_s5_ul rev16_s5_ur
    (by decide) rev16_s5_ll_mem rev16_s5_lr_mem rev16_s5_ul_mem rev16_s5_ur_mem p
    (hp _ rev16_plane55_mem) (hp _ rev16_plane9_mem) hx0 hx1
theorem rev16_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev16_planes) : rev16_s0_ll.real.1≤p.1 := by
  have hc := rev16_plane27.combine_sound rev16_plane64 15204000000 287616000000 (by decide) (by decide) p
    (hp _ rev16_plane27_mem) (hp _ rev16_plane64_mem)
  exact (rev16_plane27.combine rev16_plane64 15204000000 287616000000).xBoundCheck_sound rev16_s0_ll.nx rev16_s0_ll.dx true (by decide) p hc
theorem rev16_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev16_planes) : p.1≤rev16_s5_lr.real.1 := by
  have hc := rev16_plane9.combine_sound rev16_plane55 48252000000 2139440000000 (by decide) (by decide) p
    (hp _ rev16_plane9_mem) (hp _ rev16_plane55_mem)
  exact (rev16_plane9.combine rev16_plane55 48252000000 2139440000000).xBoundCheck_sound rev16_s5_lr.nx rev16_s5_lr.dx false (by decide) p hc
theorem rev16_hull (p : Point) (hp : p∈IntegerCarrier rev16_planes) :
    p∈rationalHull (fractionRow16.map FractionPoint.rational) := by
  have hxlo := rev16_bound0_lo p hp
  have hxhi := rev16_bound0_hi p hp
  by_cases h0 : p.1≤rev16_s0_lr.real.1
  · exact rev16_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev16_s1_lr.real.1
  · exact rev16_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev16_s2_lr.real.1
  · exact rev16_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev16_s3_lr.real.1
  · exact rev16_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p.1≤rev16_s4_lr.real.1
  · exact rev16_slab4 p hp (le_of_lt (lt_of_not_ge h3)) h4
  exact rev16_slab5 p hp (le_of_lt (lt_of_not_ge h4)) hxhi
theorem overlay_in_hull16 (p : Point)
    (hp : ∀ g, ClosedCell ((![1,2,7,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow16 := by
  rw [← fractionRow16_correct]
  exact rev16_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull16
