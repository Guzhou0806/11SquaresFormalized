import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks1
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev13_planes : List IntegerPlane := integerOverlayPlanes ![1,1,11,4]
def rev13_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev13_plane2_mem : rev13_plane2 ∈ rev13_planes := by decide
def rev13_plane6 : IntegerPlane := ⟨2083356000000,746024000000,1117516707941⟩
theorem rev13_plane6_mem : rev13_plane6 ∈ rev13_planes := by decide
def rev13_plane26 : IntegerPlane := ⟨(-2083356000000),746024000000,(-965839292059)⟩
theorem rev13_plane26_mem : rev13_plane26 ∈ rev13_planes := by decide
def rev13_plane51 : IntegerPlane := ⟨(-2112760000000),48252000000,(-982750749085)⟩
theorem rev13_plane51_mem : rev13_plane51 ∈ rev13_planes := by decide
def rev13_plane72 : IntegerPlane := ⟨2112760000000,48252000000,1130009250915⟩
theorem rev13_plane72_mem : rev13_plane72 ∈ rev13_planes := by decide
def rev13_vertex0 : FractionPoint := fractionRow13[0]!
theorem rev13_vertex0_mem : rev13_vertex0∈fractionRow13 := by decide
def rev13_vertex1 : FractionPoint := fractionRow13[1]!
theorem rev13_vertex1_mem : rev13_vertex1∈fractionRow13 := by decide
def rev13_vertex2 : FractionPoint := fractionRow13[2]!
theorem rev13_vertex2_mem : rev13_vertex2∈fractionRow13 := by decide
def rev13_vertex3 : FractionPoint := fractionRow13[3]!
theorem rev13_vertex3_mem : rev13_vertex3∈fractionRow13 := by decide
def rev13_vertex4 : FractionPoint := fractionRow13[4]!
theorem rev13_vertex4_mem : rev13_vertex4∈fractionRow13 := by decide
def rev13_s0_ll : FractionPoint := ⟨196550149817,422552000000,0,1⟩
theorem rev13_s0_ll_mem : rev13_s0_ll.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane2 rev13_vertex0 rev13_vertex1 rev13_s0_ll
    rev13_vertex0_mem rev13_vertex1_mem (by decide)
def rev13_s0_lr : FractionPoint := ⟨171637991828739293,368910893132000000,0,1⟩
theorem rev13_s0_lr_mem : rev13_s0_lr.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane2 rev13_vertex0 rev13_vertex1 rev13_s0_lr
    rev13_vertex0_mem rev13_vertex1_mem (by decide)
def rev13_s0_ul : FractionPoint := ⟨196550149817,422552000000,0,1⟩
theorem rev13_s0_ul_mem : rev13_s0_ul.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane51 rev13_vertex0 rev13_vertex4 rev13_s0_ul
    rev13_vertex0_mem rev13_vertex4_mem (by decide)
def rev13_s0_ur : FractionPoint := ⟨171637991828739293,368910893132000000,341652346007821,73782178626400000⟩
theorem rev13_s0_ur_mem : rev13_s0_ur.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane51 rev13_vertex0 rev13_vertex4 rev13_s0_ur
    rev13_vertex0_mem rev13_vertex4_mem (by decide)
theorem rev13_slab0 (p : Point) (hp : p∈IntegerCarrier rev13_planes)
    (hx0 : rev13_s0_ll.real.1≤p.1) (hx1 : p.1≤rev13_s0_lr.real.1) :
    p∈rationalHull (fractionRow13.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev13_plane2 rev13_plane51 rev13_s0_ll rev13_s0_lr rev13_s0_ul rev13_s0_ur
    (by decide) rev13_s0_ll_mem rev13_s0_lr_mem rev13_s0_ul_mem rev13_s0_ur_mem p
    (hp _ rev13_plane2_mem) (hp _ rev13_plane51_mem) hx0 hx1
def rev13_s1_ll : FractionPoint := ⟨171637991828739293,368910893132000000,0,1⟩
theorem rev13_s1_ll_mem : rev13_s1_ll.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane2 rev13_vertex0 rev13_vertex1 rev13_s1_ll
    rev13_vertex0_mem rev13_vertex1_mem (by decide)
def rev13_s1_lr : FractionPoint := ⟨1,2,0,1⟩
theorem rev13_s1_lr_mem : rev13_s1_lr.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane2 rev13_vertex0 rev13_vertex1 rev13_s1_lr
    rev13_vertex0_mem rev13_vertex1_mem (by decide)
def rev13_s1_ul : FractionPoint := ⟨171637991828739293,368910893132000000,341652346007821,73782178626400000⟩
theorem rev13_s1_ul_mem : rev13_s1_ul.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane26 rev13_vertex4 rev13_vertex3 rev13_s1_ul
    rev13_vertex4_mem rev13_vertex3_mem (by decide)
def rev13_s1_ur : FractionPoint := ⟨1,2,75838707941,746024000000⟩
theorem rev13_s1_ur_mem : rev13_s1_ur.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane26 rev13_vertex4 rev13_vertex3 rev13_s1_ur
    rev13_vertex4_mem rev13_vertex3_mem (by decide)
theorem rev13_slab1 (p : Point) (hp : p∈IntegerCarrier rev13_planes)
    (hx0 : rev13_s1_ll.real.1≤p.1) (hx1 : p.1≤rev13_s1_lr.real.1) :
    p∈rationalHull (fractionRow13.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev13_plane2 rev13_plane26 rev13_s1_ll rev13_s1_lr rev13_s1_ul rev13_s1_ur
    (by decide) rev13_s1_ll_mem rev13_s1_lr_mem rev13_s1_ul_mem rev13_s1_ur_mem p
    (hp _ rev13_plane2_mem) (hp _ rev13_plane26_mem) hx0 hx1
def rev13_s2_ll : FractionPoint := ⟨1,2,0,1⟩
theorem rev13_s2_ll_mem : rev13_s2_ll.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane2 rev13_vertex0 rev13_vertex1 rev13_s2_ll
    rev13_vertex0_mem rev13_vertex1_mem (by decide)
def rev13_s2_lr : FractionPoint := ⟨197272901303260707,368910893132000000,0,1⟩
theorem rev13_s2_lr_mem : rev13_s2_lr.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane2 rev13_vertex0 rev13_vertex1 rev13_s2_lr
    rev13_vertex0_mem rev13_vertex1_mem (by decide)
def rev13_s2_ul : FractionPoint := ⟨1,2,75838707941,746024000000⟩
theorem rev13_s2_ul_mem : rev13_s2_ul.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane6 rev13_vertex3 rev13_vertex2 rev13_s2_ul
    rev13_vertex3_mem rev13_vertex2_mem (by decide)
def rev13_s2_ur : FractionPoint := ⟨197272901303260707,368910893132000000,341652346007821,73782178626400000⟩
theorem rev13_s2_ur_mem : rev13_s2_ur.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane6 rev13_vertex3 rev13_vertex2 rev13_s2_ur
    rev13_vertex3_mem rev13_vertex2_mem (by decide)
theorem rev13_slab2 (p : Point) (hp : p∈IntegerCarrier rev13_planes)
    (hx0 : rev13_s2_ll.real.1≤p.1) (hx1 : p.1≤rev13_s2_lr.real.1) :
    p∈rationalHull (fractionRow13.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev13_plane2 rev13_plane6 rev13_s2_ll rev13_s2_lr rev13_s2_ul rev13_s2_ur
    (by decide) rev13_s2_ll_mem rev13_s2_lr_mem rev13_s2_ul_mem rev13_s2_ur_mem p
    (hp _ rev13_plane2_mem) (hp _ rev13_plane6_mem) hx0 hx1
def rev13_s3_ll : FractionPoint := ⟨197272901303260707,368910893132000000,0,1⟩
theorem rev13_s3_ll_mem : rev13_s3_ll.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane2 rev13_vertex0 rev13_vertex1 rev13_s3_ll
    rev13_vertex0_mem rev13_vertex1_mem (by decide)
def rev13_s3_lr : FractionPoint := ⟨226001850183,422552000000,0,1⟩
theorem rev13_s3_lr_mem : rev13_s3_lr.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane2 rev13_vertex0 rev13_vertex1 rev13_s3_lr
    rev13_vertex0_mem rev13_vertex1_mem (by decide)
def rev13_s3_ul : FractionPoint := ⟨197272901303260707,368910893132000000,341652346007821,73782178626400000⟩
theorem rev13_s3_ul_mem : rev13_s3_ul.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane72 rev13_vertex2 rev13_vertex1 rev13_s3_ul
    rev13_vertex2_mem rev13_vertex1_mem (by decide)
def rev13_s3_ur : FractionPoint := ⟨226001850183,422552000000,0,1⟩
theorem rev13_s3_ur_mem : rev13_s3_ur.real ∈ rationalHull (fractionRow13.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow13 rev13_plane72 rev13_vertex2 rev13_vertex1 rev13_s3_ur
    rev13_vertex2_mem rev13_vertex1_mem (by decide)
theorem rev13_slab3 (p : Point) (hp : p∈IntegerCarrier rev13_planes)
    (hx0 : rev13_s3_ll.real.1≤p.1) (hx1 : p.1≤rev13_s3_lr.real.1) :
    p∈rationalHull (fractionRow13.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev13_plane2 rev13_plane72 rev13_s3_ll rev13_s3_lr rev13_s3_ul rev13_s3_ur
    (by decide) rev13_s3_ll_mem rev13_s3_lr_mem rev13_s3_ul_mem rev13_s3_ur_mem p
    (hp _ rev13_plane2_mem) (hp _ rev13_plane72_mem) hx0 hx1
theorem rev13_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev13_planes) : rev13_s0_ll.real.1≤p.1 := by
  have hc := rev13_plane2.combine_sound rev13_plane51 48252000000 1 (by decide) (by decide) p
    (hp _ rev13_plane2_mem) (hp _ rev13_plane51_mem)
  exact (rev13_plane2.combine rev13_plane51 48252000000 1).xBoundCheck_sound rev13_s0_ll.nx rev13_s0_ll.dx true (by decide) p hc
theorem rev13_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev13_planes) : p.1≤rev13_s3_lr.real.1 := by
  have hc := rev13_plane2.combine_sound rev13_plane72 48252000000 1 (by decide) (by decide) p
    (hp _ rev13_plane2_mem) (hp _ rev13_plane72_mem)
  exact (rev13_plane2.combine rev13_plane72 48252000000 1).xBoundCheck_sound rev13_s3_lr.nx rev13_s3_lr.dx false (by decide) p hc
theorem rev13_hull (p : Point) (hp : p∈IntegerCarrier rev13_planes) :
    p∈rationalHull (fractionRow13.map FractionPoint.rational) := by
  have hxlo := rev13_bound0_lo p hp
  have hxhi := rev13_bound0_hi p hp
  by_cases h0 : p.1≤rev13_s0_lr.real.1
  · exact rev13_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev13_s1_lr.real.1
  · exact rev13_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev13_s2_lr.real.1
  · exact rev13_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev13_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull13 (p : Point)
    (hp : ∀ g, ClosedCell ((![1,1,11,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow13 := by
  rw [← fractionRow13_correct]
  exact rev13_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull13
