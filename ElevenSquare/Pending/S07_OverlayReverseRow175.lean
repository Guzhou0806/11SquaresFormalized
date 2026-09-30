import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks21
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev175_planes : List IntegerPlane := integerOverlayPlanes ![11,8,13,14]
def rev175_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev175_plane1_mem : rev175_plane1 ∈ rev175_planes := by decide
def rev175_plane19 : IntegerPlane := ⟨(-15204000000),2139684000000,1555517771568⟩
theorem rev175_plane19_mem : rev175_plane19 ∈ rev175_planes := by decide
def rev175_plane28 : IntegerPlane := ⟨48252000000,(-2112760000000),(-1081757250915)⟩
theorem rev175_plane28_mem : rev175_plane28 ∈ rev175_planes := by decide
def rev175_plane56 : IntegerPlane := ⟨287616000000,1855520000000,1643759759600⟩
theorem rev175_plane56_mem : rev175_plane56 ∈ rev175_planes := by decide
def rev175_plane58 : IntegerPlane := ⟨746024000000,(-2083356000000),(-371492707941)⟩
theorem rev175_plane58_mem : rev175_plane58 ∈ rev175_planes := by decide
def rev175_plane74 : IntegerPlane := ⟨(-2139440000000),16372000000,(-1745735152575)⟩
theorem rev175_plane74_mem : rev175_plane74 ∈ rev175_planes := by decide
def rev175_plane79 : IntegerPlane := ⟨(-699324000000),2145688000000,995724727641⟩
theorem rev175_plane79_mem : rev175_plane79 ∈ rev175_planes := by decide
def rev175_vertex0 : FractionPoint := fractionRow175[0]!
theorem rev175_vertex0_mem : rev175_vertex0∈fractionRow175 := by decide
def rev175_vertex1 : FractionPoint := fractionRow175[1]!
theorem rev175_vertex1_mem : rev175_vertex1∈fractionRow175 := by decide
def rev175_vertex2 : FractionPoint := fractionRow175[2]!
theorem rev175_vertex2_mem : rev175_vertex2∈fractionRow175 := by decide
def rev175_vertex3 : FractionPoint := fractionRow175[3]!
theorem rev175_vertex3_mem : rev175_vertex3∈fractionRow175 := by decide
def rev175_vertex4 : FractionPoint := fractionRow175[4]!
theorem rev175_vertex4_mem : rev175_vertex4∈fractionRow175 := by decide
def rev175_vertex5 : FractionPoint := fractionRow175[5]!
theorem rev175_vertex5_mem : rev175_vertex5∈fractionRow175 := by decide
def rev175_vertex6 : FractionPoint := fractionRow175[6]!
theorem rev175_vertex6_mem : rev175_vertex6∈fractionRow175 := by decide
def rev175_s0_ll : FractionPoint := ⟨185301496533316869,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev175_s0_ll_mem : rev175_s0_ll.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane28 rev175_vertex5 rev175_vertex6 rev175_s0_ll
    rev175_vertex5_mem rev175_vertex6_mem (by decide)
def rev175_s0_lr : FractionPoint := ⟨940526243324821263,1144780350548000000,20058698706300371395839,37791345834746757500000⟩
theorem rev175_s0_lr_mem : rev175_s0_lr.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane28 rev175_vertex5 rev175_vertex6 rev175_s0_lr
    rev175_vertex5_mem rev175_vertex6_mem (by decide)
def rev175_s0_ul : FractionPoint := ⟨185301496533316869,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev175_s0_ul_mem : rev175_s0_ul.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane74 rev175_vertex5 rev175_vertex4 rev175_s0_ul
    rev175_vertex5_mem rev175_vertex4_mem (by decide)
def rev175_s0_ur : FractionPoint := ⟨940526243324821263,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev175_s0_ur_mem : rev175_s0_ur.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane74 rev175_vertex5 rev175_vertex4 rev175_s0_ur
    rev175_vertex5_mem rev175_vertex4_mem (by decide)
theorem rev175_slab0 (p : Point) (hp : p∈IntegerCarrier rev175_planes)
    (hx0 : rev175_s0_ll.real.1≤p.1) (hx1 : p.1≤rev175_s0_lr.real.1) :
    p∈rationalHull (fractionRow175.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev175_plane28 rev175_plane74 rev175_s0_ll rev175_s0_lr rev175_s0_ul rev175_s0_ur
    (by decide) rev175_s0_ll_mem rev175_s0_lr_mem rev175_s0_ul_mem rev175_s0_ur_mem p
    (hp _ rev175_plane28_mem) (hp _ rev175_plane74_mem) hx0 hx1
def rev175_s1_ll : FractionPoint := ⟨940526243324821263,1144780350548000000,20058698706300371395839,37791345834746757500000⟩
theorem rev175_s1_ll_mem : rev175_s1_ll.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane28 rev175_vertex5 rev175_vertex6 rev175_s1_ll
    rev175_vertex5_mem rev175_vertex6_mem (by decide)
def rev175_s1_lr : FractionPoint := ⟨20118659135039889,24395155554400000,1710025121797217591019,3221319303069634000000⟩
theorem rev175_s1_lr_mem : rev175_s1_lr.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane28 rev175_vertex5 rev175_vertex6 rev175_s1_lr
    rev175_vertex5_mem rev175_vertex6_mem (by decide)
def rev175_s1_ul : FractionPoint := ⟨940526243324821263,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev175_s1_ul_mem : rev175_s1_ul.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane79 rev175_vertex4 rev175_vertex3 rev175_s1_ul
    rev175_vertex4_mem rev175_vertex3_mem (by decide)
def rev175_s1_ur : FractionPoint := ⟨20118659135039889,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev175_s1_ur_mem : rev175_s1_ur.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane79 rev175_vertex4 rev175_vertex3 rev175_s1_ur
    rev175_vertex4_mem rev175_vertex3_mem (by decide)
theorem rev175_slab1 (p : Point) (hp : p∈IntegerCarrier rev175_planes)
    (hx0 : rev175_s1_ll.real.1≤p.1) (hx1 : p.1≤rev175_s1_lr.real.1) :
    p∈rationalHull (fractionRow175.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev175_plane28 rev175_plane79 rev175_s1_ll rev175_s1_lr rev175_s1_ul rev175_s1_ur
    (by decide) rev175_s1_ll_mem rev175_s1_lr_mem rev175_s1_ul_mem rev175_s1_ur_mem p
    (hp _ rev175_plane28_mem) (hp _ rev175_plane79_mem) hx0 hx1
def rev175_s2_ll : FractionPoint := ⟨20118659135039889,24395155554400000,1710025121797217591019,3221319303069634000000⟩
theorem rev175_s2_ll_mem : rev175_s2_ll.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane28 rev175_vertex5 rev175_vertex6 rev175_s2_ll
    rev175_vertex5_mem rev175_vertex6_mem (by decide)
def rev175_s2_lr : FractionPoint := ⟨657116793708449,670436124400000,378478169187535517487,708235313093672000000⟩
theorem rev175_s2_lr_mem : rev175_s2_lr.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane28 rev175_vertex5 rev175_vertex6 rev175_s2_lr
    rev175_vertex5_mem rev175_vertex6_mem (by decide)
def rev175_s2_ul : FractionPoint := ⟨20118659135039889,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev175_s2_ul_mem : rev175_s2_ul.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane19 rev175_vertex3 rev175_vertex2 rev175_s2_ul
    rev175_vertex3_mem rev175_vertex2_mem (by decide)
def rev175_s2_ur : FractionPoint := ⟨657116793708449,670436124400000,351475835396027,478882946000000⟩
theorem rev175_s2_ur_mem : rev175_s2_ur.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane19 rev175_vertex3 rev175_vertex2 rev175_s2_ur
    rev175_vertex3_mem rev175_vertex2_mem (by decide)
theorem rev175_slab2 (p : Point) (hp : p∈IntegerCarrier rev175_planes)
    (hx0 : rev175_s2_ll.real.1≤p.1) (hx1 : p.1≤rev175_s2_lr.real.1) :
    p∈rationalHull (fractionRow175.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev175_plane28 rev175_plane19 rev175_s2_ll rev175_s2_lr rev175_s2_ul rev175_s2_ur
    (by decide) rev175_s2_ll_mem rev175_s2_lr_mem rev175_s2_ul_mem rev175_s2_ur_mem p
    (hp _ rev175_plane28_mem) (hp _ rev175_plane19_mem) hx0 hx1
def rev175_s3_ll : FractionPoint := ⟨657116793708449,670436124400000,378478169187535517487,708235313093672000000⟩
theorem rev175_s3_ll_mem : rev175_s3_ll.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane28 rev175_vertex5 rev175_vertex6 rev175_s3_ll
    rev175_vertex5_mem rev175_vertex6_mem (by decide)
def rev175_s3_lr : FractionPoint := ⟨73440526280392179,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev175_s3_lr_mem : rev175_s3_lr.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane28 rev175_vertex5 rev175_vertex6 rev175_s3_lr
    rev175_vertex5_mem rev175_vertex6_mem (by decide)
def rev175_s3_ul : FractionPoint := ⟨657116793708449,670436124400000,351475835396027,478882946000000⟩
theorem rev175_s3_ul_mem : rev175_s3_ul.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane56 rev175_vertex2 rev175_vertex1 rev175_s3_ul
    rev175_vertex2_mem rev175_vertex1_mem (by decide)
def rev175_s3_ur : FractionPoint := ⟨73440526280392179,73782178626400000,1564961028047410082159,2139129813825902000000⟩
theorem rev175_s3_ur_mem : rev175_s3_ur.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane56 rev175_vertex2 rev175_vertex1 rev175_s3_ur
    rev175_vertex2_mem rev175_vertex1_mem (by decide)
theorem rev175_slab3 (p : Point) (hp : p∈IntegerCarrier rev175_planes)
    (hx0 : rev175_s3_ll.real.1≤p.1) (hx1 : p.1≤rev175_s3_lr.real.1) :
    p∈rationalHull (fractionRow175.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev175_plane28 rev175_plane56 rev175_s3_ll rev175_s3_lr rev175_s3_ul rev175_s3_ur
    (by decide) rev175_s3_ll_mem rev175_s3_lr_mem rev175_s3_ul_mem rev175_s3_ur_mem p
    (hp _ rev175_plane28_mem) (hp _ rev175_plane56_mem) hx0 hx1
def rev175_s4_ll : FractionPoint := ⟨73440526280392179,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev175_s4_ll_mem : rev175_s4_ll.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane58 rev175_vertex6 rev175_vertex0 rev175_s4_ll
    rev175_vertex6_mem rev175_vertex0_mem (by decide)
def rev175_s4_lr : FractionPoint := ⟨1,1,1117516707941,2083356000000⟩
theorem rev175_s4_lr_mem : rev175_s4_lr.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane58 rev175_vertex6 rev175_vertex0 rev175_s4_lr
    rev175_vertex6_mem rev175_vertex0_mem (by decide)
def rev175_s4_ul : FractionPoint := ⟨73440526280392179,73782178626400000,1564961028047410082159,2139129813825902000000⟩
theorem rev175_s4_ul_mem : rev175_s4_ul.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane56 rev175_vertex2 rev175_vertex1 rev175_s4_ul
    rev175_vertex2_mem rev175_vertex1_mem (by decide)
def rev175_s4_ur : FractionPoint := ⟨1,1,3390359399,4638800000⟩
theorem rev175_s4_ur_mem : rev175_s4_ur.real ∈ rationalHull (fractionRow175.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow175 rev175_plane56 rev175_vertex2 rev175_vertex1 rev175_s4_ur
    rev175_vertex2_mem rev175_vertex1_mem (by decide)
theorem rev175_slab4 (p : Point) (hp : p∈IntegerCarrier rev175_planes)
    (hx0 : rev175_s4_ll.real.1≤p.1) (hx1 : p.1≤rev175_s4_lr.real.1) :
    p∈rationalHull (fractionRow175.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev175_plane58 rev175_plane56 rev175_s4_ll rev175_s4_lr rev175_s4_ul rev175_s4_ur
    (by decide) rev175_s4_ll_mem rev175_s4_lr_mem rev175_s4_ul_mem rev175_s4_ur_mem p
    (hp _ rev175_plane58_mem) (hp _ rev175_plane56_mem) hx0 hx1
theorem rev175_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev175_planes) : rev175_s0_ll.real.1≤p.1 := by
  have hc := rev175_plane28.combine_sound rev175_plane74 16372000000 2112760000000 (by decide) (by decide) p
    (hp _ rev175_plane28_mem) (hp _ rev175_plane74_mem)
  exact (rev175_plane28.combine rev175_plane74 16372000000 2112760000000).xBoundCheck_sound rev175_s0_ll.nx rev175_s0_ll.dx true (by decide) p hc
theorem rev175_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev175_planes) : p.1≤rev175_s4_lr.real.1 := by
  have hc := rev175_plane1.combine_sound rev175_plane1 1 0 (by decide) (by decide) p
    (hp _ rev175_plane1_mem) (hp _ rev175_plane1_mem)
  exact (rev175_plane1.combine rev175_plane1 1 0).xBoundCheck_sound rev175_s4_lr.nx rev175_s4_lr.dx false (by decide) p hc
theorem rev175_hull (p : Point) (hp : p∈IntegerCarrier rev175_planes) :
    p∈rationalHull (fractionRow175.map FractionPoint.rational) := by
  have hxlo := rev175_bound0_lo p hp
  have hxhi := rev175_bound0_hi p hp
  by_cases h0 : p.1≤rev175_s0_lr.real.1
  · exact rev175_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev175_s1_lr.real.1
  · exact rev175_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev175_s2_lr.real.1
  · exact rev175_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev175_s3_lr.real.1
  · exact rev175_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev175_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull175 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,8,13,14] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow175 := by
  rw [← fractionRow175_correct]
  exact rev175_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull175
