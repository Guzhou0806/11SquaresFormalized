import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks24
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev196_planes : List IntegerPlane := integerOverlayPlanes ![13,14,4,7]
def rev196_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev196_plane3_mem : rev196_plane3 ∈ rev196_planes := by decide
def rev196_plane16 : IntegerPlane := ⟨(-1855520000000),287616000000,(-211760240400)⟩
theorem rev196_plane16_mem : rev196_plane16 ∈ rev196_planes := by decide
def rev196_plane18 : IntegerPlane := ⟨2083356000000,746024000000,1711863292059⟩
theorem rev196_plane18_mem : rev196_plane18 ∈ rev196_planes := by decide
def rev196_plane34 : IntegerPlane := ⟨(-16372000000),(-2139440000000),(-1762107152575)⟩
theorem rev196_plane34_mem : rev196_plane34 ∈ rev196_planes := by decide
def rev196_plane39 : IntegerPlane := ⟨(-2145688000000),(-699324000000),(-1149963272359)⟩
theorem rev196_plane39_mem : rev196_plane39 ∈ rev196_planes := by decide
def rev196_plane44 : IntegerPlane := ⟨(-2139684000000),(-15204000000),(-584166228432)⟩
theorem rev196_plane44_mem : rev196_plane44 ∈ rev196_planes := by decide
def rev196_plane75 : IntegerPlane := ⟨2112760000000,48252000000,1031002749085⟩
theorem rev196_plane75_mem : rev196_plane75 ∈ rev196_planes := by decide
def rev196_vertex0 : FractionPoint := fractionRow196[0]!
theorem rev196_vertex0_mem : rev196_vertex0∈fractionRow196 := by decide
def rev196_vertex1 : FractionPoint := fractionRow196[1]!
theorem rev196_vertex1_mem : rev196_vertex1∈fractionRow196 := by decide
def rev196_vertex2 : FractionPoint := fractionRow196[2]!
theorem rev196_vertex2_mem : rev196_vertex2∈fractionRow196 := by decide
def rev196_vertex3 : FractionPoint := fractionRow196[3]!
theorem rev196_vertex3_mem : rev196_vertex3∈fractionRow196 := by decide
def rev196_vertex4 : FractionPoint := fractionRow196[4]!
theorem rev196_vertex4_mem : rev196_vertex4∈fractionRow196 := by decide
def rev196_vertex5 : FractionPoint := fractionRow196[5]!
theorem rev196_vertex5_mem : rev196_vertex5∈fractionRow196 := by decide
def rev196_vertex6 : FractionPoint := fractionRow196[6]!
theorem rev196_vertex6_mem : rev196_vertex6∈fractionRow196 := by decide
def rev196_s0_ll : FractionPoint := ⟨127407110603973,478882946000000,657116793708449,670436124400000⟩
theorem rev196_s0_ll_mem : rev196_s0_ll.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane44 rev196_vertex2 rev196_vertex3 rev196_s0_ll
    rev196_vertex2_mem rev196_vertex3_mem (by decide)
def rev196_s0_lr : FractionPoint := ⟨32586451828252811,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev196_s0_lr_mem : rev196_s0_lr.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane44 rev196_vertex2 rev196_vertex3 rev196_s0_lr
    rev196_vertex2_mem rev196_vertex3_mem (by decide)
def rev196_s0_ul : FractionPoint := ⟨127407110603973,478882946000000,657116793708449,670436124400000⟩
theorem rev196_s0_ul_mem : rev196_s0_ul.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane16 rev196_vertex2 rev196_vertex1 rev196_s0_ul
    rev196_vertex2_mem rev196_vertex1_mem (by decide)
def rev196_s0_ur : FractionPoint := ⟨32586451828252811,121975777772000000,216469956702399746737,219263658122947200000⟩
theorem rev196_s0_ur_mem : rev196_s0_ur.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane16 rev196_vertex2 rev196_vertex1 rev196_s0_ur
    rev196_vertex2_mem rev196_vertex1_mem (by decide)
theorem rev196_slab0 (p : Point) (hp : p∈IntegerCarrier rev196_planes)
    (hx0 : rev196_s0_ll.real.1≤p.1) (hx1 : p.1≤rev196_s0_lr.real.1) :
    p∈rationalHull (fractionRow196.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev196_plane44 rev196_plane16 rev196_s0_ll rev196_s0_lr rev196_s0_ul rev196_s0_ur
    (by decide) rev196_s0_ll_mem rev196_s0_lr_mem rev196_s0_ul_mem rev196_s0_ur_mem p
    (hp _ rev196_plane44_mem) (hp _ rev196_plane16_mem) hx0 hx1
def rev196_s1_ll : FractionPoint := ⟨32586451828252811,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev196_s1_ll_mem : rev196_s1_ll.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane39 rev196_vertex3 rev196_vertex4 rev196_s1_ll
    rev196_vertex3_mem rev196_vertex4_mem (by decide)
def rev196_s1_lr : FractionPoint := ⟨61399680052418983,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev196_s1_lr_mem : rev196_s1_lr.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane39 rev196_vertex3 rev196_vertex4 rev196_s1_lr
    rev196_vertex3_mem rev196_vertex4_mem (by decide)
def rev196_s1_ul : FractionPoint := ⟨32586451828252811,121975777772000000,216469956702399746737,219263658122947200000⟩
theorem rev196_s1_ul_mem : rev196_s1_ul.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane16 rev196_vertex2 rev196_vertex1 rev196_s1_ul
    rev196_vertex2_mem rev196_vertex1_mem (by decide)
def rev196_s1_ur : FractionPoint := ⟨61399680052418983,228956070109600000,409028386771352006177,411571431629016960000⟩
theorem rev196_s1_ur_mem : rev196_s1_ur.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane16 rev196_vertex2 rev196_vertex1 rev196_s1_ur
    rev196_vertex2_mem rev196_vertex1_mem (by decide)
theorem rev196_slab1 (p : Point) (hp : p∈IntegerCarrier rev196_planes)
    (hx0 : rev196_s1_ll.real.1≤p.1) (hx1 : p.1≤rev196_s1_lr.real.1) :
    p∈rationalHull (fractionRow196.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev196_plane39 rev196_plane16 rev196_s1_ll rev196_s1_lr rev196_s1_ul rev196_s1_ur
    (by decide) rev196_s1_ll_mem rev196_s1_lr_mem rev196_s1_ul_mem rev196_s1_ur_mem p
    (hp _ rev196_plane39_mem) (hp _ rev196_plane16_mem) hx0 hx1
def rev196_s2_ll : FractionPoint := ⟨61399680052418983,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev196_s2_ll_mem : rev196_s2_ll.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane34 rev196_vertex4 rev196_vertex5 rev196_s2_ll
    rev196_vertex4_mem rev196_vertex5_mem (by decide)
def rev196_s2_lr : FractionPoint := ⟨1248440601,4638800000,4076811594922669,4962217136000000⟩
theorem rev196_s2_lr_mem : rev196_s2_lr.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane34 rev196_vertex4 rev196_vertex5 rev196_s2_lr
    rev196_vertex4_mem rev196_vertex5_mem (by decide)
def rev196_s2_ul : FractionPoint := ⟨61399680052418983,228956070109600000,409028386771352006177,411571431629016960000⟩
theorem rev196_s2_ul_mem : rev196_s2_ul.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane16 rev196_vertex2 rev196_vertex1 rev196_s2_ul
    rev196_vertex2_mem rev196_vertex1_mem (by decide)
def rev196_s2_ur : FractionPoint := ⟨1248440601,4638800000,1,1⟩
theorem rev196_s2_ur_mem : rev196_s2_ur.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane16 rev196_vertex2 rev196_vertex1 rev196_s2_ur
    rev196_vertex2_mem rev196_vertex1_mem (by decide)
theorem rev196_slab2 (p : Point) (hp : p∈IntegerCarrier rev196_planes)
    (hx0 : rev196_s2_ll.real.1≤p.1) (hx1 : p.1≤rev196_s2_lr.real.1) :
    p∈rationalHull (fractionRow196.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev196_plane34 rev196_plane16 rev196_s2_ll rev196_s2_lr rev196_s2_ul rev196_s2_ur
    (by decide) rev196_s2_ll_mem rev196_s2_lr_mem rev196_s2_ul_mem rev196_s2_ur_mem p
    (hp _ rev196_plane34_mem) (hp _ rev196_plane16_mem) hx0 hx1
def rev196_s3_ll : FractionPoint := ⟨1248440601,4638800000,4076811594922669,4962217136000000⟩
theorem rev196_s3_ll_mem : rev196_s3_ll.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane34 rev196_vertex4 rev196_vertex5 rev196_s3_ll
    rev196_vertex4_mem rev196_vertex5_mem (by decide)
def rev196_s3_lr : FractionPoint := ⟨965839292059,2083356000000,456910473508806469,557151895080000000⟩
theorem rev196_s3_lr_mem : rev196_s3_lr.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane34 rev196_vertex4 rev196_vertex5 rev196_s3_lr
    rev196_vertex4_mem rev196_vertex5_mem (by decide)
def rev196_s3_ul : FractionPoint := ⟨1248440601,4638800000,1,1⟩
theorem rev196_s3_ul_mem : rev196_s3_ul.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane3 rev196_vertex1 rev196_vertex0 rev196_s3_ul
    rev196_vertex1_mem rev196_vertex0_mem (by decide)
def rev196_s3_ur : FractionPoint := ⟨965839292059,2083356000000,1,1⟩
theorem rev196_s3_ur_mem : rev196_s3_ur.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane3 rev196_vertex1 rev196_vertex0 rev196_s3_ur
    rev196_vertex1_mem rev196_vertex0_mem (by decide)
theorem rev196_slab3 (p : Point) (hp : p∈IntegerCarrier rev196_planes)
    (hx0 : rev196_s3_ll.real.1≤p.1) (hx1 : p.1≤rev196_s3_lr.real.1) :
    p∈rationalHull (fractionRow196.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev196_plane34 rev196_plane3 rev196_s3_ll rev196_s3_lr rev196_s3_ul rev196_s3_ur
    (by decide) rev196_s3_ll_mem rev196_s3_lr_mem rev196_s3_ul_mem rev196_s3_ur_mem p
    (hp _ rev196_plane34_mem) (hp _ rev196_plane3_mem) hx0 hx1
def rev196_s4_ll : FractionPoint := ⟨965839292059,2083356000000,456910473508806469,557151895080000000⟩
theorem rev196_s4_ll_mem : rev196_s4_ll.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane34 rev196_vertex4 rev196_vertex5 rev196_s4_ll
    rev196_vertex4_mem rev196_vertex5_mem (by decide)
def rev196_s4_lr : FractionPoint := ⟨171637991828739293,368910893132000000,40453154140531782744369,49328920075145380000000⟩
theorem rev196_s4_lr_mem : rev196_s4_lr.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane34 rev196_vertex4 rev196_vertex5 rev196_s4_lr
    rev196_vertex4_mem rev196_vertex5_mem (by decide)
def rev196_s4_ul : FractionPoint := ⟨965839292059,2083356000000,1,1⟩
theorem rev196_s4_ul_mem : rev196_s4_ul.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane18 rev196_vertex0 rev196_vertex6 rev196_s4_ul
    rev196_vertex0_mem rev196_vertex6_mem (by decide)
def rev196_s4_ur : FractionPoint := ⟨171637991828739293,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev196_s4_ur_mem : rev196_s4_ur.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane18 rev196_vertex0 rev196_vertex6 rev196_s4_ur
    rev196_vertex0_mem rev196_vertex6_mem (by decide)
theorem rev196_slab4 (p : Point) (hp : p∈IntegerCarrier rev196_planes)
    (hx0 : rev196_s4_ll.real.1≤p.1) (hx1 : p.1≤rev196_s4_lr.real.1) :
    p∈rationalHull (fractionRow196.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev196_plane34 rev196_plane18 rev196_s4_ll rev196_s4_lr rev196_s4_ul rev196_s4_ur
    (by decide) rev196_s4_ll_mem rev196_s4_lr_mem rev196_s4_ul_mem rev196_s4_ur_mem p
    (hp _ rev196_plane34_mem) (hp _ rev196_plane18_mem) hx0 hx1
def rev196_s5_ll : FractionPoint := ⟨171637991828739293,368910893132000000,40453154140531782744369,49328920075145380000000⟩
theorem rev196_s5_ll_mem : rev196_s5_ll.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane34 rev196_vertex4 rev196_vertex5 rev196_s5_ll
    rev196_vertex4_mem rev196_vertex5_mem (by decide)
def rev196_s5_lr : FractionPoint := ⟨4241486654352727,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev196_s5_lr_mem : rev196_s5_lr.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane34 rev196_vertex4 rev196_vertex5 rev196_s5_lr
    rev196_vertex4_mem rev196_vertex5_mem (by decide)
def rev196_s5_ul : FractionPoint := ⟨171637991828739293,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev196_s5_ul_mem : rev196_s5_ul.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane75 rev196_vertex6 rev196_vertex5 rev196_s5_ul
    rev196_vertex6_mem rev196_vertex5_mem (by decide)
def rev196_s5_ur : FractionPoint := ⟨4241486654352727,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev196_s5_ur_mem : rev196_s5_ur.real ∈ rationalHull (fractionRow196.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow196 rev196_plane75 rev196_vertex6 rev196_vertex5 rev196_s5_ur
    rev196_vertex6_mem rev196_vertex5_mem (by decide)
theorem rev196_slab5 (p : Point) (hp : p∈IntegerCarrier rev196_planes)
    (hx0 : rev196_s5_ll.real.1≤p.1) (hx1 : p.1≤rev196_s5_lr.real.1) :
    p∈rationalHull (fractionRow196.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev196_plane34 rev196_plane75 rev196_s5_ll rev196_s5_lr rev196_s5_ul rev196_s5_ur
    (by decide) rev196_s5_ll_mem rev196_s5_lr_mem rev196_s5_ul_mem rev196_s5_ur_mem p
    (hp _ rev196_plane34_mem) (hp _ rev196_plane75_mem) hx0 hx1
theorem rev196_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev196_planes) : rev196_s0_ll.real.1≤p.1 := by
  have hc := rev196_plane16.combine_sound rev196_plane44 15204000000 287616000000 (by decide) (by decide) p
    (hp _ rev196_plane16_mem) (hp _ rev196_plane44_mem)
  exact (rev196_plane16.combine rev196_plane44 15204000000 287616000000).xBoundCheck_sound rev196_s0_ll.nx rev196_s0_ll.dx true (by decide) p hc
theorem rev196_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev196_planes) : p.1≤rev196_s5_lr.real.1 := by
  have hc := rev196_plane34.combine_sound rev196_plane75 48252000000 2139440000000 (by decide) (by decide) p
    (hp _ rev196_plane34_mem) (hp _ rev196_plane75_mem)
  exact (rev196_plane34.combine rev196_plane75 48252000000 2139440000000).xBoundCheck_sound rev196_s5_lr.nx rev196_s5_lr.dx false (by decide) p hc
theorem rev196_hull (p : Point) (hp : p∈IntegerCarrier rev196_planes) :
    p∈rationalHull (fractionRow196.map FractionPoint.rational) := by
  have hxlo := rev196_bound0_lo p hp
  have hxhi := rev196_bound0_hi p hp
  by_cases h0 : p.1≤rev196_s0_lr.real.1
  · exact rev196_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev196_s1_lr.real.1
  · exact rev196_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev196_s2_lr.real.1
  · exact rev196_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev196_s3_lr.real.1
  · exact rev196_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p.1≤rev196_s4_lr.real.1
  · exact rev196_slab4 p hp (le_of_lt (lt_of_not_ge h3)) h4
  exact rev196_slab5 p hp (le_of_lt (lt_of_not_ge h4)) hxhi
theorem overlay_in_hull196 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,14,4,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow196 := by
  rw [← fractionRow196_correct]
  exact rev196_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull196
