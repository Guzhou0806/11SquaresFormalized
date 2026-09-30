import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks25
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev203_planes : List IntegerPlane := integerOverlayPlanes ![14,13,8,11]
def rev203_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev203_plane3_mem : rev203_plane3 ∈ rev203_planes := by decide
def rev203_plane14 : IntegerPlane := ⟨16372000000,(-2139440000000),(-1745735152575)⟩
theorem rev203_plane14_mem : rev203_plane14 ∈ rev203_planes := by decide
def rev203_plane19 : IntegerPlane := ⟨2145688000000,(-699324000000),995724727641⟩
theorem rev203_plane19_mem : rev203_plane19 ∈ rev203_planes := by decide
def rev203_plane36 : IntegerPlane := ⟨1855520000000,287616000000,1643759759600⟩
theorem rev203_plane36_mem : rev203_plane36 ∈ rev203_planes := by decide
def rev203_plane38 : IntegerPlane := ⟨(-2083356000000),746024000000,(-371492707941)⟩
theorem rev203_plane38_mem : rev203_plane38 ∈ rev203_planes := by decide
def rev203_plane48 : IntegerPlane := ⟨(-2112760000000),48252000000,(-1081757250915)⟩
theorem rev203_plane48_mem : rev203_plane48 ∈ rev203_planes := by decide
def rev203_plane79 : IntegerPlane := ⟨2139684000000,(-15204000000),1555517771568⟩
theorem rev203_plane79_mem : rev203_plane79 ∈ rev203_planes := by decide
def rev203_vertex0 : FractionPoint := fractionRow203[0]!
theorem rev203_vertex0_mem : rev203_vertex0∈fractionRow203 := by decide
def rev203_vertex1 : FractionPoint := fractionRow203[1]!
theorem rev203_vertex1_mem : rev203_vertex1∈fractionRow203 := by decide
def rev203_vertex2 : FractionPoint := fractionRow203[2]!
theorem rev203_vertex2_mem : rev203_vertex2∈fractionRow203 := by decide
def rev203_vertex3 : FractionPoint := fractionRow203[3]!
theorem rev203_vertex3_mem : rev203_vertex3∈fractionRow203 := by decide
def rev203_vertex4 : FractionPoint := fractionRow203[4]!
theorem rev203_vertex4_mem : rev203_vertex4∈fractionRow203 := by decide
def rev203_vertex5 : FractionPoint := fractionRow203[5]!
theorem rev203_vertex5_mem : rev203_vertex5∈fractionRow203 := by decide
def rev203_vertex6 : FractionPoint := fractionRow203[6]!
theorem rev203_vertex6_mem : rev203_vertex6∈fractionRow203 := by decide
def rev203_s0_ll : FractionPoint := ⟨4797179890959273,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev203_s0_ll_mem : rev203_s0_ll.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane14 rev203_vertex3 rev203_vertex4 rev203_s0_ll
    rev203_vertex3_mem rev203_vertex4_mem (by decide)
def rev203_s0_lr : FractionPoint := ⟨197272901303260707,368910893132000000,40453154140531782744369,49328920075145380000000⟩
theorem rev203_s0_lr_mem : rev203_s0_lr.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane14 rev203_vertex3 rev203_vertex4 rev203_s0_lr
    rev203_vertex3_mem rev203_vertex4_mem (by decide)
def rev203_s0_ul : FractionPoint := ⟨4797179890959273,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev203_s0_ul_mem : rev203_s0_ul.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane48 rev203_vertex3 rev203_vertex2 rev203_s0_ul
    rev203_vertex3_mem rev203_vertex2_mem (by decide)
def rev203_s0_ur : FractionPoint := ⟨197272901303260707,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev203_s0_ur_mem : rev203_s0_ur.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane48 rev203_vertex3 rev203_vertex2 rev203_s0_ur
    rev203_vertex3_mem rev203_vertex2_mem (by decide)
theorem rev203_slab0 (p : Point) (hp : p∈IntegerCarrier rev203_planes)
    (hx0 : rev203_s0_ll.real.1≤p.1) (hx1 : p.1≤rev203_s0_lr.real.1) :
    p∈rationalHull (fractionRow203.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev203_plane14 rev203_plane48 rev203_s0_ll rev203_s0_lr rev203_s0_ul rev203_s0_ur
    (by decide) rev203_s0_ll_mem rev203_s0_lr_mem rev203_s0_ul_mem rev203_s0_ur_mem p
    (hp _ rev203_plane14_mem) (hp _ rev203_plane48_mem) hx0 hx1
def rev203_s1_ll : FractionPoint := ⟨197272901303260707,368910893132000000,40453154140531782744369,49328920075145380000000⟩
theorem rev203_s1_ll_mem : rev203_s1_ll.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane14 rev203_vertex3 rev203_vertex4 rev203_s1_ll
    rev203_vertex3_mem rev203_vertex4_mem (by decide)
def rev203_s1_lr : FractionPoint := ⟨1117516707941,2083356000000,456910473508806469,557151895080000000⟩
theorem rev203_s1_lr_mem : rev203_s1_lr.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane14 rev203_vertex3 rev203_vertex4 rev203_s1_lr
    rev203_vertex3_mem rev203_vertex4_mem (by decide)
def rev203_s1_ul : FractionPoint := ⟨197272901303260707,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev203_s1_ul_mem : rev203_s1_ul.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane38 rev203_vertex2 rev203_vertex1 rev203_s1_ul
    rev203_vertex2_mem rev203_vertex1_mem (by decide)
def rev203_s1_ur : FractionPoint := ⟨1117516707941,2083356000000,1,1⟩
theorem rev203_s1_ur_mem : rev203_s1_ur.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane38 rev203_vertex2 rev203_vertex1 rev203_s1_ur
    rev203_vertex2_mem rev203_vertex1_mem (by decide)
theorem rev203_slab1 (p : Point) (hp : p∈IntegerCarrier rev203_planes)
    (hx0 : rev203_s1_ll.real.1≤p.1) (hx1 : p.1≤rev203_s1_lr.real.1) :
    p∈rationalHull (fractionRow203.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev203_plane14 rev203_plane38 rev203_s1_ll rev203_s1_lr rev203_s1_ul rev203_s1_ur
    (by decide) rev203_s1_ll_mem rev203_s1_lr_mem rev203_s1_ul_mem rev203_s1_ur_mem p
    (hp _ rev203_plane14_mem) (hp _ rev203_plane38_mem) hx0 hx1
def rev203_s2_ll : FractionPoint := ⟨1117516707941,2083356000000,456910473508806469,557151895080000000⟩
theorem rev203_s2_ll_mem : rev203_s2_ll.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane14 rev203_vertex3 rev203_vertex4 rev203_s2_ll
    rev203_vertex3_mem rev203_vertex4_mem (by decide)
def rev203_s2_lr : FractionPoint := ⟨3390359399,4638800000,4076811594922669,4962217136000000⟩
theorem rev203_s2_lr_mem : rev203_s2_lr.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane14 rev203_vertex3 rev203_vertex4 rev203_s2_lr
    rev203_vertex3_mem rev203_vertex4_mem (by decide)
def rev203_s2_ul : FractionPoint := ⟨1117516707941,2083356000000,1,1⟩
theorem rev203_s2_ul_mem : rev203_s2_ul.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane3 rev203_vertex1 rev203_vertex0 rev203_s2_ul
    rev203_vertex1_mem rev203_vertex0_mem (by decide)
def rev203_s2_ur : FractionPoint := ⟨3390359399,4638800000,1,1⟩
theorem rev203_s2_ur_mem : rev203_s2_ur.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane3 rev203_vertex1 rev203_vertex0 rev203_s2_ur
    rev203_vertex1_mem rev203_vertex0_mem (by decide)
theorem rev203_slab2 (p : Point) (hp : p∈IntegerCarrier rev203_planes)
    (hx0 : rev203_s2_ll.real.1≤p.1) (hx1 : p.1≤rev203_s2_lr.real.1) :
    p∈rationalHull (fractionRow203.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev203_plane14 rev203_plane3 rev203_s2_ll rev203_s2_lr rev203_s2_ul rev203_s2_ur
    (by decide) rev203_s2_ll_mem rev203_s2_lr_mem rev203_s2_ul_mem rev203_s2_ur_mem p
    (hp _ rev203_plane14_mem) (hp _ rev203_plane3_mem) hx0 hx1
def rev203_s3_ll : FractionPoint := ⟨3390359399,4638800000,4076811594922669,4962217136000000⟩
theorem rev203_s3_ll_mem : rev203_s3_ll.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane14 rev203_vertex3 rev203_vertex4 rev203_s3_ll
    rev203_vertex3_mem rev203_vertex4_mem (by decide)
def rev203_s3_lr : FractionPoint := ⟨167556390057181017,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev203_s3_lr_mem : rev203_s3_lr.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane14 rev203_vertex3 rev203_vertex4 rev203_s3_lr
    rev203_vertex3_mem rev203_vertex4_mem (by decide)
def rev203_s3_ul : FractionPoint := ⟨3390359399,4638800000,1,1⟩
theorem rev203_s3_ul_mem : rev203_s3_ul.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane36 rev203_vertex0 rev203_vertex6 rev203_s3_ul
    rev203_vertex0_mem rev203_vertex6_mem (by decide)
def rev203_s3_ur : FractionPoint := ⟨167556390057181017,228956070109600000,409028386771352006177,411571431629016960000⟩
theorem rev203_s3_ur_mem : rev203_s3_ur.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane36 rev203_vertex0 rev203_vertex6 rev203_s3_ur
    rev203_vertex0_mem rev203_vertex6_mem (by decide)
theorem rev203_slab3 (p : Point) (hp : p∈IntegerCarrier rev203_planes)
    (hx0 : rev203_s3_ll.real.1≤p.1) (hx1 : p.1≤rev203_s3_lr.real.1) :
    p∈rationalHull (fractionRow203.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev203_plane14 rev203_plane36 rev203_s3_ll rev203_s3_lr rev203_s3_ul rev203_s3_ur
    (by decide) rev203_s3_ll_mem rev203_s3_lr_mem rev203_s3_ul_mem rev203_s3_ur_mem p
    (hp _ rev203_plane14_mem) (hp _ rev203_plane36_mem) hx0 hx1
def rev203_s4_ll : FractionPoint := ⟨167556390057181017,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev203_s4_ll_mem : rev203_s4_ll.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane19 rev203_vertex4 rev203_vertex5 rev203_s4_ll
    rev203_vertex4_mem rev203_vertex5_mem (by decide)
def rev203_s4_lr : FractionPoint := ⟨89389325943747189,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev203_s4_lr_mem : rev203_s4_lr.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane19 rev203_vertex4 rev203_vertex5 rev203_s4_lr
    rev203_vertex4_mem rev203_vertex5_mem (by decide)
def rev203_s4_ul : FractionPoint := ⟨167556390057181017,228956070109600000,409028386771352006177,411571431629016960000⟩
theorem rev203_s4_ul_mem : rev203_s4_ul.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane36 rev203_vertex0 rev203_vertex6 rev203_s4_ul
    rev203_vertex0_mem rev203_vertex6_mem (by decide)
def rev203_s4_ur : FractionPoint := ⟨89389325943747189,121975777772000000,216469956702399746737,219263658122947200000⟩
theorem rev203_s4_ur_mem : rev203_s4_ur.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane36 rev203_vertex0 rev203_vertex6 rev203_s4_ur
    rev203_vertex0_mem rev203_vertex6_mem (by decide)
theorem rev203_slab4 (p : Point) (hp : p∈IntegerCarrier rev203_planes)
    (hx0 : rev203_s4_ll.real.1≤p.1) (hx1 : p.1≤rev203_s4_lr.real.1) :
    p∈rationalHull (fractionRow203.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev203_plane19 rev203_plane36 rev203_s4_ll rev203_s4_lr rev203_s4_ul rev203_s4_ur
    (by decide) rev203_s4_ll_mem rev203_s4_lr_mem rev203_s4_ul_mem rev203_s4_ur_mem p
    (hp _ rev203_plane19_mem) (hp _ rev203_plane36_mem) hx0 hx1
def rev203_s5_ll : FractionPoint := ⟨89389325943747189,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev203_s5_ll_mem : rev203_s5_ll.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane79 rev203_vertex5 rev203_vertex6 rev203_s5_ll
    rev203_vertex5_mem rev203_vertex6_mem (by decide)
def rev203_s5_lr : FractionPoint := ⟨351475835396027,478882946000000,657116793708449,670436124400000⟩
theorem rev203_s5_lr_mem : rev203_s5_lr.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane79 rev203_vertex5 rev203_vertex6 rev203_s5_lr
    rev203_vertex5_mem rev203_vertex6_mem (by decide)
def rev203_s5_ul : FractionPoint := ⟨89389325943747189,121975777772000000,216469956702399746737,219263658122947200000⟩
theorem rev203_s5_ul_mem : rev203_s5_ul.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane36 rev203_vertex0 rev203_vertex6 rev203_s5_ul
    rev203_vertex0_mem rev203_vertex6_mem (by decide)
def rev203_s5_ur : FractionPoint := ⟨351475835396027,478882946000000,657116793708449,670436124400000⟩
theorem rev203_s5_ur_mem : rev203_s5_ur.real ∈ rationalHull (fractionRow203.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow203 rev203_plane36 rev203_vertex0 rev203_vertex6 rev203_s5_ur
    rev203_vertex0_mem rev203_vertex6_mem (by decide)
theorem rev203_slab5 (p : Point) (hp : p∈IntegerCarrier rev203_planes)
    (hx0 : rev203_s5_ll.real.1≤p.1) (hx1 : p.1≤rev203_s5_lr.real.1) :
    p∈rationalHull (fractionRow203.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev203_plane79 rev203_plane36 rev203_s5_ll rev203_s5_lr rev203_s5_ul rev203_s5_ur
    (by decide) rev203_s5_ll_mem rev203_s5_lr_mem rev203_s5_ul_mem rev203_s5_ur_mem p
    (hp _ rev203_plane79_mem) (hp _ rev203_plane36_mem) hx0 hx1
theorem rev203_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev203_planes) : rev203_s0_ll.real.1≤p.1 := by
  have hc := rev203_plane14.combine_sound rev203_plane48 48252000000 2139440000000 (by decide) (by decide) p
    (hp _ rev203_plane14_mem) (hp _ rev203_plane48_mem)
  exact (rev203_plane14.combine rev203_plane48 48252000000 2139440000000).xBoundCheck_sound rev203_s0_ll.nx rev203_s0_ll.dx true (by decide) p hc
theorem rev203_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev203_planes) : p.1≤rev203_s5_lr.real.1 := by
  have hc := rev203_plane36.combine_sound rev203_plane79 15204000000 287616000000 (by decide) (by decide) p
    (hp _ rev203_plane36_mem) (hp _ rev203_plane79_mem)
  exact (rev203_plane36.combine rev203_plane79 15204000000 287616000000).xBoundCheck_sound rev203_s5_lr.nx rev203_s5_lr.dx false (by decide) p hc
theorem rev203_hull (p : Point) (hp : p∈IntegerCarrier rev203_planes) :
    p∈rationalHull (fractionRow203.map FractionPoint.rational) := by
  have hxlo := rev203_bound0_lo p hp
  have hxhi := rev203_bound0_hi p hp
  by_cases h0 : p.1≤rev203_s0_lr.real.1
  · exact rev203_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev203_s1_lr.real.1
  · exact rev203_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev203_s2_lr.real.1
  · exact rev203_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev203_s3_lr.real.1
  · exact rev203_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p.1≤rev203_s4_lr.real.1
  · exact rev203_slab4 p hp (le_of_lt (lt_of_not_ge h3)) h4
  exact rev203_slab5 p hp (le_of_lt (lt_of_not_ge h4)) hxhi
theorem overlay_in_hull203 (p : Point)
    (hp : ∀ g, ClosedCell ((![14,13,8,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow203 := by
  rw [← fractionRow203_correct]
  exact rev203_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull203
