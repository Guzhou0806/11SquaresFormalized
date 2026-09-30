import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks25
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev206_planes : List IntegerPlane := integerOverlayPlanes ![14,14,4,11]
def rev206_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev206_plane3_mem : rev206_plane3 ∈ rev206_planes := by decide
def rev206_plane17 : IntegerPlane := ⟨(-2083356000000),(-746024000000),(-1711863292059)⟩
theorem rev206_plane17_mem : rev206_plane17 ∈ rev206_planes := by decide
def rev206_plane37 : IntegerPlane := ⟨2083356000000,(-746024000000),371492707941⟩
theorem rev206_plane37_mem : rev206_plane37 ∈ rev206_planes := by decide
def rev206_plane52 : IntegerPlane := ⟨2112760000000,(-48252000000),1081757250915⟩
theorem rev206_plane52_mem : rev206_plane52 ∈ rev206_planes := by decide
def rev206_plane71 : IntegerPlane := ⟨(-2112760000000),(-48252000000),(-1031002749085)⟩
theorem rev206_plane71_mem : rev206_plane71 ∈ rev206_planes := by decide
def rev206_vertex0 : FractionPoint := fractionRow206[0]!
theorem rev206_vertex0_mem : rev206_vertex0∈fractionRow206 := by decide
def rev206_vertex1 : FractionPoint := fractionRow206[1]!
theorem rev206_vertex1_mem : rev206_vertex1∈fractionRow206 := by decide
def rev206_vertex2 : FractionPoint := fractionRow206[2]!
theorem rev206_vertex2_mem : rev206_vertex2∈fractionRow206 := by decide
def rev206_vertex3 : FractionPoint := fractionRow206[3]!
theorem rev206_vertex3_mem : rev206_vertex3∈fractionRow206 := by decide
def rev206_vertex4 : FractionPoint := fractionRow206[4]!
theorem rev206_vertex4_mem : rev206_vertex4∈fractionRow206 := by decide
def rev206_s0_ll : FractionPoint := ⟨196550149817,422552000000,1,1⟩
theorem rev206_s0_ll_mem : rev206_s0_ll.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane71 rev206_vertex1 rev206_vertex2 rev206_s0_ll
    rev206_vertex1_mem rev206_vertex2_mem (by decide)
def rev206_s0_lr : FractionPoint := ⟨171637991828739293,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev206_s0_lr_mem : rev206_s0_lr.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane71 rev206_vertex1 rev206_vertex2 rev206_s0_lr
    rev206_vertex1_mem rev206_vertex2_mem (by decide)
def rev206_s0_ul : FractionPoint := ⟨196550149817,422552000000,1,1⟩
theorem rev206_s0_ul_mem : rev206_s0_ul.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane3 rev206_vertex1 rev206_vertex0 rev206_s0_ul
    rev206_vertex1_mem rev206_vertex0_mem (by decide)
def rev206_s0_ur : FractionPoint := ⟨171637991828739293,368910893132000000,1,1⟩
theorem rev206_s0_ur_mem : rev206_s0_ur.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane3 rev206_vertex1 rev206_vertex0 rev206_s0_ur
    rev206_vertex1_mem rev206_vertex0_mem (by decide)
theorem rev206_slab0 (p : Point) (hp : p∈IntegerCarrier rev206_planes)
    (hx0 : rev206_s0_ll.real.1≤p.1) (hx1 : p.1≤rev206_s0_lr.real.1) :
    p∈rationalHull (fractionRow206.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev206_plane71 rev206_plane3 rev206_s0_ll rev206_s0_lr rev206_s0_ul rev206_s0_ur
    (by decide) rev206_s0_ll_mem rev206_s0_lr_mem rev206_s0_ul_mem rev206_s0_ur_mem p
    (hp _ rev206_plane71_mem) (hp _ rev206_plane3_mem) hx0 hx1
def rev206_s1_ll : FractionPoint := ⟨171637991828739293,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev206_s1_ll_mem : rev206_s1_ll.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane17 rev206_vertex2 rev206_vertex3 rev206_s1_ll
    rev206_vertex2_mem rev206_vertex3_mem (by decide)
def rev206_s1_lr : FractionPoint := ⟨1,2,670185292059,746024000000⟩
theorem rev206_s1_lr_mem : rev206_s1_lr.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane17 rev206_vertex2 rev206_vertex3 rev206_s1_lr
    rev206_vertex2_mem rev206_vertex3_mem (by decide)
def rev206_s1_ul : FractionPoint := ⟨171637991828739293,368910893132000000,1,1⟩
theorem rev206_s1_ul_mem : rev206_s1_ul.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane3 rev206_vertex1 rev206_vertex0 rev206_s1_ul
    rev206_vertex1_mem rev206_vertex0_mem (by decide)
def rev206_s1_ur : FractionPoint := ⟨1,2,1,1⟩
theorem rev206_s1_ur_mem : rev206_s1_ur.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane3 rev206_vertex1 rev206_vertex0 rev206_s1_ur
    rev206_vertex1_mem rev206_vertex0_mem (by decide)
theorem rev206_slab1 (p : Point) (hp : p∈IntegerCarrier rev206_planes)
    (hx0 : rev206_s1_ll.real.1≤p.1) (hx1 : p.1≤rev206_s1_lr.real.1) :
    p∈rationalHull (fractionRow206.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev206_plane17 rev206_plane3 rev206_s1_ll rev206_s1_lr rev206_s1_ul rev206_s1_ur
    (by decide) rev206_s1_ll_mem rev206_s1_lr_mem rev206_s1_ul_mem rev206_s1_ur_mem p
    (hp _ rev206_plane17_mem) (hp _ rev206_plane3_mem) hx0 hx1
def rev206_s2_ll : FractionPoint := ⟨1,2,670185292059,746024000000⟩
theorem rev206_s2_ll_mem : rev206_s2_ll.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane37 rev206_vertex3 rev206_vertex4 rev206_s2_ll
    rev206_vertex3_mem rev206_vertex4_mem (by decide)
def rev206_s2_lr : FractionPoint := ⟨197272901303260707,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev206_s2_lr_mem : rev206_s2_lr.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane37 rev206_vertex3 rev206_vertex4 rev206_s2_lr
    rev206_vertex3_mem rev206_vertex4_mem (by decide)
def rev206_s2_ul : FractionPoint := ⟨1,2,1,1⟩
theorem rev206_s2_ul_mem : rev206_s2_ul.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane3 rev206_vertex1 rev206_vertex0 rev206_s2_ul
    rev206_vertex1_mem rev206_vertex0_mem (by decide)
def rev206_s2_ur : FractionPoint := ⟨197272901303260707,368910893132000000,1,1⟩
theorem rev206_s2_ur_mem : rev206_s2_ur.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane3 rev206_vertex1 rev206_vertex0 rev206_s2_ur
    rev206_vertex1_mem rev206_vertex0_mem (by decide)
theorem rev206_slab2 (p : Point) (hp : p∈IntegerCarrier rev206_planes)
    (hx0 : rev206_s2_ll.real.1≤p.1) (hx1 : p.1≤rev206_s2_lr.real.1) :
    p∈rationalHull (fractionRow206.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev206_plane37 rev206_plane3 rev206_s2_ll rev206_s2_lr rev206_s2_ul rev206_s2_ur
    (by decide) rev206_s2_ll_mem rev206_s2_lr_mem rev206_s2_ul_mem rev206_s2_ur_mem p
    (hp _ rev206_plane37_mem) (hp _ rev206_plane3_mem) hx0 hx1
def rev206_s3_ll : FractionPoint := ⟨197272901303260707,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev206_s3_ll_mem : rev206_s3_ll.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane52 rev206_vertex4 rev206_vertex0 rev206_s3_ll
    rev206_vertex4_mem rev206_vertex0_mem (by decide)
def rev206_s3_lr : FractionPoint := ⟨226001850183,422552000000,1,1⟩
theorem rev206_s3_lr_mem : rev206_s3_lr.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane52 rev206_vertex4 rev206_vertex0 rev206_s3_lr
    rev206_vertex4_mem rev206_vertex0_mem (by decide)
def rev206_s3_ul : FractionPoint := ⟨197272901303260707,368910893132000000,1,1⟩
theorem rev206_s3_ul_mem : rev206_s3_ul.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane3 rev206_vertex1 rev206_vertex0 rev206_s3_ul
    rev206_vertex1_mem rev206_vertex0_mem (by decide)
def rev206_s3_ur : FractionPoint := ⟨226001850183,422552000000,1,1⟩
theorem rev206_s3_ur_mem : rev206_s3_ur.real ∈ rationalHull (fractionRow206.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow206 rev206_plane3 rev206_vertex1 rev206_vertex0 rev206_s3_ur
    rev206_vertex1_mem rev206_vertex0_mem (by decide)
theorem rev206_slab3 (p : Point) (hp : p∈IntegerCarrier rev206_planes)
    (hx0 : rev206_s3_ll.real.1≤p.1) (hx1 : p.1≤rev206_s3_lr.real.1) :
    p∈rationalHull (fractionRow206.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev206_plane52 rev206_plane3 rev206_s3_ll rev206_s3_lr rev206_s3_ul rev206_s3_ur
    (by decide) rev206_s3_ll_mem rev206_s3_lr_mem rev206_s3_ul_mem rev206_s3_ur_mem p
    (hp _ rev206_plane52_mem) (hp _ rev206_plane3_mem) hx0 hx1
theorem rev206_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev206_planes) : rev206_s0_ll.real.1≤p.1 := by
  have hc := rev206_plane3.combine_sound rev206_plane71 48252000000 1 (by decide) (by decide) p
    (hp _ rev206_plane3_mem) (hp _ rev206_plane71_mem)
  exact (rev206_plane3.combine rev206_plane71 48252000000 1).xBoundCheck_sound rev206_s0_ll.nx rev206_s0_ll.dx true (by decide) p hc
theorem rev206_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev206_planes) : p.1≤rev206_s3_lr.real.1 := by
  have hc := rev206_plane3.combine_sound rev206_plane52 48252000000 1 (by decide) (by decide) p
    (hp _ rev206_plane3_mem) (hp _ rev206_plane52_mem)
  exact (rev206_plane3.combine rev206_plane52 48252000000 1).xBoundCheck_sound rev206_s3_lr.nx rev206_s3_lr.dx false (by decide) p hc
theorem rev206_hull (p : Point) (hp : p∈IntegerCarrier rev206_planes) :
    p∈rationalHull (fractionRow206.map FractionPoint.rational) := by
  have hxlo := rev206_bound0_lo p hp
  have hxhi := rev206_bound0_hi p hp
  by_cases h0 : p.1≤rev206_s0_lr.real.1
  · exact rev206_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev206_s1_lr.real.1
  · exact rev206_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev206_s2_lr.real.1
  · exact rev206_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev206_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull206 (p : Point)
    (hp : ∀ g, ClosedCell ((![14,14,4,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow206 := by
  rw [← fractionRow206_correct]
  exact rev206_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull206
