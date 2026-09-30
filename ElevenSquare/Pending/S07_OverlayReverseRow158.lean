import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks19
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev158_planes : List IntegerPlane := integerOverlayPlanes ![10,13,4,11]
def rev158_plane17 : IntegerPlane := ⟨(-2099728000000),1393416000000,33871860516⟩
theorem rev158_plane17_mem : rev158_plane17 ∈ rev158_planes := by decide
def rev158_plane18 : IntegerPlane := ⟨(-16372000000),2139440000000,1745735152575⟩
theorem rev158_plane18_mem : rev158_plane18 ∈ rev158_planes := by decide
def rev158_plane34 : IntegerPlane := ⟨(-2099728000000),(-1393416000000),(-2133599860516)⟩
theorem rev158_plane34_mem : rev158_plane34 ∈ rev158_planes := by decide
def rev158_plane52 : IntegerPlane := ⟨2112760000000,(-48252000000),1081757250915⟩
theorem rev158_plane52_mem : rev158_plane52 ∈ rev158_planes := by decide
def rev158_plane53 : IntegerPlane := ⟨1468788000000,(-2093220000000),(-880675273104)⟩
theorem rev158_plane53_mem : rev158_plane53 ∈ rev158_planes := by decide
def rev158_vertex0 : FractionPoint := fractionRow158[0]!
theorem rev158_vertex0_mem : rev158_vertex0∈fractionRow158 := by decide
def rev158_vertex1 : FractionPoint := fractionRow158[1]!
theorem rev158_vertex1_mem : rev158_vertex1∈fractionRow158 := by decide
def rev158_vertex2 : FractionPoint := fractionRow158[2]!
theorem rev158_vertex2_mem : rev158_vertex2∈fractionRow158 := by decide
def rev158_vertex3 : FractionPoint := fractionRow158[3]!
theorem rev158_vertex3_mem : rev158_vertex3∈fractionRow158 := by decide
def rev158_vertex4 : FractionPoint := fractionRow158[4]!
theorem rev158_vertex4_mem : rev158_vertex4∈fractionRow158 := by decide
def rev158_s0_ll : FractionPoint := ⟨1,2,270933965129,348354000000⟩
theorem rev158_s0_ll_mem : rev158_s0_ll.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane34 rev158_vertex1 rev158_vertex2 rev158_s0_ll
    rev158_vertex1_mem rev158_vertex2_mem (by decide)
def rev158_s0_lr : FractionPoint := ⟨22492686692234849,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev158_s0_lr_mem : rev158_s0_lr.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane34 rev158_vertex1 rev158_vertex2 rev158_s0_lr
    rev158_vertex1_mem rev158_vertex2_mem (by decide)
def rev158_s0_ul : FractionPoint := ⟨1,2,270933965129,348354000000⟩
theorem rev158_s0_ul_mem : rev158_s0_ul.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane17 rev158_vertex1 rev158_vertex0 rev158_s0_ul
    rev158_vertex1_mem rev158_vertex0_mem (by decide)
def rev158_s0_ur : FractionPoint := ⟨22492686692234849,44734898222000000,6092972284460741927953,7791790367613294000000⟩
theorem rev158_s0_ur_mem : rev158_s0_ur.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane17 rev158_vertex1 rev158_vertex0 rev158_s0_ur
    rev158_vertex1_mem rev158_vertex0_mem (by decide)
theorem rev158_slab0 (p : Point) (hp : p∈IntegerCarrier rev158_planes)
    (hx0 : rev158_s0_ll.real.1≤p.1) (hx1 : p.1≤rev158_s0_lr.real.1) :
    p∈rationalHull (fractionRow158.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev158_plane34 rev158_plane17 rev158_s0_ll rev158_s0_lr rev158_s0_ul rev158_s0_ur
    (by decide) rev158_s0_ll_mem rev158_s0_lr_mem rev158_s0_ul_mem rev158_s0_ur_mem p
    (hp _ rev158_plane34_mem) (hp _ rev158_plane17_mem) hx0 hx1
def rev158_s1_ll : FractionPoint := ⟨22492686692234849,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev158_s1_ll_mem : rev158_s1_ll.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane53 rev158_vertex2 rev158_vertex3 rev158_s1_ll
    rev158_vertex2_mem rev158_vertex3_mem (by decide)
def rev158_s1_lr : FractionPoint := ⟨59001712002452379,111735726639200000,77109957559212238716137,97453107381544260000000⟩
theorem rev158_s1_lr_mem : rev158_s1_lr.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane53 rev158_vertex2 rev158_vertex3 rev158_s1_lr
    rev158_vertex2_mem rev158_vertex3_mem (by decide)
def rev158_s1_ul : FractionPoint := ⟨22492686692234849,44734898222000000,6092972284460741927953,7791790367613294000000⟩
theorem rev158_s1_ul_mem : rev158_s1_ul.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane17 rev158_vertex1 rev158_vertex0 rev158_s1_ul
    rev158_vertex1_mem rev158_vertex0_mem (by decide)
def rev158_s1_ur : FractionPoint := ⟨59001712002452379,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev158_s1_ur_mem : rev158_s1_ur.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane17 rev158_vertex1 rev158_vertex0 rev158_s1_ur
    rev158_vertex1_mem rev158_vertex0_mem (by decide)
theorem rev158_slab1 (p : Point) (hp : p∈IntegerCarrier rev158_planes)
    (hx0 : rev158_s1_ll.real.1≤p.1) (hx1 : p.1≤rev158_s1_lr.real.1) :
    p∈rationalHull (fractionRow158.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev158_plane53 rev158_plane17 rev158_s1_ll rev158_s1_lr rev158_s1_ul rev158_s1_ur
    (by decide) rev158_s1_ll_mem rev158_s1_lr_mem rev158_s1_ul_mem rev158_s1_ur_mem p
    (hp _ rev158_plane53_mem) (hp _ rev158_plane17_mem) hx0 hx1
def rev158_s2_ll : FractionPoint := ⟨59001712002452379,111735726639200000,77109957559212238716137,97453107381544260000000⟩
theorem rev158_s2_ll_mem : rev158_s2_ll.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane53 rev158_vertex2 rev158_vertex3 rev158_s2_ll
    rev158_vertex2_mem rev158_vertex3_mem (by decide)
def rev158_s2_lr : FractionPoint := ⟨64079173778836403,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev158_s2_lr_mem : rev158_s2_lr.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane53 rev158_vertex2 rev158_vertex3 rev158_s2_lr
    rev158_vertex2_mem rev158_vertex3_mem (by decide)
def rev158_s2_ul : FractionPoint := ⟨59001712002452379,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev158_s2_ul_mem : rev158_s2_ul.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane18 rev158_vertex0 rev158_vertex4 rev158_s2_ul
    rev158_vertex0_mem rev158_vertex4_mem (by decide)
def rev158_s2_ur : FractionPoint := ⟨64079173778836403,120877764684000000,13254354200415924765701,16163170304721060000000⟩
theorem rev158_s2_ur_mem : rev158_s2_ur.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane18 rev158_vertex0 rev158_vertex4 rev158_s2_ur
    rev158_vertex0_mem rev158_vertex4_mem (by decide)
theorem rev158_slab2 (p : Point) (hp : p∈IntegerCarrier rev158_planes)
    (hx0 : rev158_s2_ll.real.1≤p.1) (hx1 : p.1≤rev158_s2_lr.real.1) :
    p∈rationalHull (fractionRow158.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev158_plane53 rev158_plane18 rev158_s2_ll rev158_s2_lr rev158_s2_ul rev158_s2_ur
    (by decide) rev158_s2_ll_mem rev158_s2_lr_mem rev158_s2_ul_mem rev158_s2_ur_mem p
    (hp _ rev158_plane53_mem) (hp _ rev158_plane18_mem) hx0 hx1
def rev158_s3_ll : FractionPoint := ⟨64079173778836403,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev158_s3_ll_mem : rev158_s3_ll.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane52 rev158_vertex3 rev158_vertex4 rev158_s3_ll
    rev158_vertex3_mem rev158_vertex4_mem (by decide)
def rev158_s3_lr : FractionPoint := ⟨4797179890959273,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev158_s3_lr_mem : rev158_s3_lr.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane52 rev158_vertex3 rev158_vertex4 rev158_s3_lr
    rev158_vertex3_mem rev158_vertex4_mem (by decide)
def rev158_s3_ul : FractionPoint := ⟨64079173778836403,120877764684000000,13254354200415924765701,16163170304721060000000⟩
theorem rev158_s3_ul_mem : rev158_s3_ul.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane18 rev158_vertex0 rev158_vertex4 rev158_s3_ul
    rev158_vertex0_mem rev158_vertex4_mem (by decide)
def rev158_s3_ur : FractionPoint := ⟨4797179890959273,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev158_s3_ur_mem : rev158_s3_ur.real ∈ rationalHull (fractionRow158.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow158 rev158_plane18 rev158_vertex0 rev158_vertex4 rev158_s3_ur
    rev158_vertex0_mem rev158_vertex4_mem (by decide)
theorem rev158_slab3 (p : Point) (hp : p∈IntegerCarrier rev158_planes)
    (hx0 : rev158_s3_ll.real.1≤p.1) (hx1 : p.1≤rev158_s3_lr.real.1) :
    p∈rationalHull (fractionRow158.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev158_plane52 rev158_plane18 rev158_s3_ll rev158_s3_lr rev158_s3_ul rev158_s3_ur
    (by decide) rev158_s3_ll_mem rev158_s3_lr_mem rev158_s3_ul_mem rev158_s3_ur_mem p
    (hp _ rev158_plane52_mem) (hp _ rev158_plane18_mem) hx0 hx1
theorem rev158_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev158_planes) : rev158_s0_ll.real.1≤p.1 := by
  have hc := rev158_plane17.combine_sound rev158_plane34 1393416000000 1393416000000 (by decide) (by decide) p
    (hp _ rev158_plane17_mem) (hp _ rev158_plane34_mem)
  exact (rev158_plane17.combine rev158_plane34 1393416000000 1393416000000).xBoundCheck_sound rev158_s0_ll.nx rev158_s0_ll.dx true (by decide) p hc
theorem rev158_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev158_planes) : p.1≤rev158_s3_lr.real.1 := by
  have hc := rev158_plane18.combine_sound rev158_plane52 48252000000 2139440000000 (by decide) (by decide) p
    (hp _ rev158_plane18_mem) (hp _ rev158_plane52_mem)
  exact (rev158_plane18.combine rev158_plane52 48252000000 2139440000000).xBoundCheck_sound rev158_s3_lr.nx rev158_s3_lr.dx false (by decide) p hc
theorem rev158_hull (p : Point) (hp : p∈IntegerCarrier rev158_planes) :
    p∈rationalHull (fractionRow158.map FractionPoint.rational) := by
  have hxlo := rev158_bound0_lo p hp
  have hxhi := rev158_bound0_hi p hp
  by_cases h0 : p.1≤rev158_s0_lr.real.1
  · exact rev158_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev158_s1_lr.real.1
  · exact rev158_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev158_s2_lr.real.1
  · exact rev158_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev158_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull158 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,13,4,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow158 := by
  rw [← fractionRow158_correct]
  exact rev158_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull158
