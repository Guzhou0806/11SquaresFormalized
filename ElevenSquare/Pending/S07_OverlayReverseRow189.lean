import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks23
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev189_planes : List IntegerPlane := integerOverlayPlanes ![13,10,4,11]
def rev189_plane14 : IntegerPlane := ⟨2099728000000,(-1393416000000),(-33871860516)⟩
theorem rev189_plane14_mem : rev189_plane14 ∈ rev189_planes := by decide
def rev189_plane37 : IntegerPlane := ⟨2099728000000,1393416000000,2133599860516⟩
theorem rev189_plane37_mem : rev189_plane37 ∈ rev189_planes := by decide
def rev189_plane38 : IntegerPlane := ⟨16372000000,2139440000000,1762107152575⟩
theorem rev189_plane38_mem : rev189_plane38 ∈ rev189_planes := by decide
def rev189_plane70 : IntegerPlane := ⟨(-1468788000000),(-2093220000000),(-2349463273104)⟩
theorem rev189_plane70_mem : rev189_plane70 ∈ rev189_planes := by decide
def rev189_plane71 : IntegerPlane := ⟨(-2112760000000),(-48252000000),(-1031002749085)⟩
theorem rev189_plane71_mem : rev189_plane71 ∈ rev189_planes := by decide
def rev189_vertex0 : FractionPoint := fractionRow189[0]!
theorem rev189_vertex0_mem : rev189_vertex0∈fractionRow189 := by decide
def rev189_vertex1 : FractionPoint := fractionRow189[1]!
theorem rev189_vertex1_mem : rev189_vertex1∈fractionRow189 := by decide
def rev189_vertex2 : FractionPoint := fractionRow189[2]!
theorem rev189_vertex2_mem : rev189_vertex2∈fractionRow189 := by decide
def rev189_vertex3 : FractionPoint := fractionRow189[3]!
theorem rev189_vertex3_mem : rev189_vertex3∈fractionRow189 := by decide
def rev189_vertex4 : FractionPoint := fractionRow189[4]!
theorem rev189_vertex4_mem : rev189_vertex4∈fractionRow189 := by decide
def rev189_s0_ll : FractionPoint := ⟨4241486654352727,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev189_s0_ll_mem : rev189_s0_ll.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane71 rev189_vertex3 rev189_vertex4 rev189_s0_ll
    rev189_vertex3_mem rev189_vertex4_mem (by decide)
def rev189_s0_lr : FractionPoint := ⟨56798590905163597,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev189_s0_lr_mem : rev189_s0_lr.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane71 rev189_vertex3 rev189_vertex4 rev189_s0_lr
    rev189_vertex3_mem rev189_vertex4_mem (by decide)
def rev189_s0_ul : FractionPoint := ⟨4241486654352727,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev189_s0_ul_mem : rev189_s0_ul.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane38 rev189_vertex3 rev189_vertex2 rev189_s0_ul
    rev189_vertex3_mem rev189_vertex2_mem (by decide)
def rev189_s0_ur : FractionPoint := ⟨56798590905163597,120877764684000000,13254354200415924765701,16163170304721060000000⟩
theorem rev189_s0_ur_mem : rev189_s0_ur.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane38 rev189_vertex3 rev189_vertex2 rev189_s0_ur
    rev189_vertex3_mem rev189_vertex2_mem (by decide)
theorem rev189_slab0 (p : Point) (hp : p∈IntegerCarrier rev189_planes)
    (hx0 : rev189_s0_ll.real.1≤p.1) (hx1 : p.1≤rev189_s0_lr.real.1) :
    p∈rationalHull (fractionRow189.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev189_plane71 rev189_plane38 rev189_s0_ll rev189_s0_lr rev189_s0_ul rev189_s0_ur
    (by decide) rev189_s0_ll_mem rev189_s0_lr_mem rev189_s0_ul_mem rev189_s0_ur_mem p
    (hp _ rev189_plane71_mem) (hp _ rev189_plane38_mem) hx0 hx1
def rev189_s1_ll : FractionPoint := ⟨56798590905163597,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev189_s1_ll_mem : rev189_s1_ll.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane70 rev189_vertex4 rev189_vertex0 rev189_s1_ll
    rev189_vertex4_mem rev189_vertex0_mem (by decide)
def rev189_s1_lr : FractionPoint := ⟨52734014636747621,111735726639200000,77109957559212238716137,97453107381544260000000⟩
theorem rev189_s1_lr_mem : rev189_s1_lr.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane70 rev189_vertex4 rev189_vertex0 rev189_s1_lr
    rev189_vertex4_mem rev189_vertex0_mem (by decide)
def rev189_s1_ul : FractionPoint := ⟨56798590905163597,120877764684000000,13254354200415924765701,16163170304721060000000⟩
theorem rev189_s1_ul_mem : rev189_s1_ul.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane38 rev189_vertex3 rev189_vertex2 rev189_s1_ul
    rev189_vertex3_mem rev189_vertex2_mem (by decide)
def rev189_s1_ur : FractionPoint := ⟨52734014636747621,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev189_s1_ur_mem : rev189_s1_ur.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane38 rev189_vertex3 rev189_vertex2 rev189_s1_ur
    rev189_vertex3_mem rev189_vertex2_mem (by decide)
theorem rev189_slab1 (p : Point) (hp : p∈IntegerCarrier rev189_planes)
    (hx0 : rev189_s1_ll.real.1≤p.1) (hx1 : p.1≤rev189_s1_lr.real.1) :
    p∈rationalHull (fractionRow189.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev189_plane70 rev189_plane38 rev189_s1_ll rev189_s1_lr rev189_s1_ul rev189_s1_ur
    (by decide) rev189_s1_ll_mem rev189_s1_lr_mem rev189_s1_ul_mem rev189_s1_ur_mem p
    (hp _ rev189_plane70_mem) (hp _ rev189_plane38_mem) hx0 hx1
def rev189_s2_ll : FractionPoint := ⟨52734014636747621,111735726639200000,77109957559212238716137,97453107381544260000000⟩
theorem rev189_s2_ll_mem : rev189_s2_ll.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane70 rev189_vertex4 rev189_vertex0 rev189_s2_ll
    rev189_vertex4_mem rev189_vertex0_mem (by decide)
def rev189_s2_lr : FractionPoint := ⟨22242211529765151,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev189_s2_lr_mem : rev189_s2_lr.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane70 rev189_vertex4 rev189_vertex0 rev189_s2_lr
    rev189_vertex4_mem rev189_vertex0_mem (by decide)
def rev189_s2_ul : FractionPoint := ⟨52734014636747621,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev189_s2_ul_mem : rev189_s2_ul.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane37 rev189_vertex2 rev189_vertex1 rev189_s2_ul
    rev189_vertex2_mem rev189_vertex1_mem (by decide)
def rev189_s2_ur : FractionPoint := ⟨22242211529765151,44734898222000000,6092972284460741927953,7791790367613294000000⟩
theorem rev189_s2_ur_mem : rev189_s2_ur.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane37 rev189_vertex2 rev189_vertex1 rev189_s2_ur
    rev189_vertex2_mem rev189_vertex1_mem (by decide)
theorem rev189_slab2 (p : Point) (hp : p∈IntegerCarrier rev189_planes)
    (hx0 : rev189_s2_ll.real.1≤p.1) (hx1 : p.1≤rev189_s2_lr.real.1) :
    p∈rationalHull (fractionRow189.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev189_plane70 rev189_plane37 rev189_s2_ll rev189_s2_lr rev189_s2_ul rev189_s2_ur
    (by decide) rev189_s2_ll_mem rev189_s2_lr_mem rev189_s2_ul_mem rev189_s2_ur_mem p
    (hp _ rev189_plane70_mem) (hp _ rev189_plane37_mem) hx0 hx1
def rev189_s3_ll : FractionPoint := ⟨22242211529765151,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev189_s3_ll_mem : rev189_s3_ll.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane14 rev189_vertex0 rev189_vertex1 rev189_s3_ll
    rev189_vertex0_mem rev189_vertex1_mem (by decide)
def rev189_s3_lr : FractionPoint := ⟨1,2,270933965129,348354000000⟩
theorem rev189_s3_lr_mem : rev189_s3_lr.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane14 rev189_vertex0 rev189_vertex1 rev189_s3_lr
    rev189_vertex0_mem rev189_vertex1_mem (by decide)
def rev189_s3_ul : FractionPoint := ⟨22242211529765151,44734898222000000,6092972284460741927953,7791790367613294000000⟩
theorem rev189_s3_ul_mem : rev189_s3_ul.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane37 rev189_vertex2 rev189_vertex1 rev189_s3_ul
    rev189_vertex2_mem rev189_vertex1_mem (by decide)
def rev189_s3_ur : FractionPoint := ⟨1,2,270933965129,348354000000⟩
theorem rev189_s3_ur_mem : rev189_s3_ur.real ∈ rationalHull (fractionRow189.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow189 rev189_plane37 rev189_vertex2 rev189_vertex1 rev189_s3_ur
    rev189_vertex2_mem rev189_vertex1_mem (by decide)
theorem rev189_slab3 (p : Point) (hp : p∈IntegerCarrier rev189_planes)
    (hx0 : rev189_s3_ll.real.1≤p.1) (hx1 : p.1≤rev189_s3_lr.real.1) :
    p∈rationalHull (fractionRow189.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev189_plane14 rev189_plane37 rev189_s3_ll rev189_s3_lr rev189_s3_ul rev189_s3_ur
    (by decide) rev189_s3_ll_mem rev189_s3_lr_mem rev189_s3_ul_mem rev189_s3_ur_mem p
    (hp _ rev189_plane14_mem) (hp _ rev189_plane37_mem) hx0 hx1
theorem rev189_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev189_planes) : rev189_s0_ll.real.1≤p.1 := by
  have hc := rev189_plane38.combine_sound rev189_plane71 48252000000 2139440000000 (by decide) (by decide) p
    (hp _ rev189_plane38_mem) (hp _ rev189_plane71_mem)
  exact (rev189_plane38.combine rev189_plane71 48252000000 2139440000000).xBoundCheck_sound rev189_s0_ll.nx rev189_s0_ll.dx true (by decide) p hc
theorem rev189_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev189_planes) : p.1≤rev189_s3_lr.real.1 := by
  have hc := rev189_plane14.combine_sound rev189_plane37 1393416000000 1393416000000 (by decide) (by decide) p
    (hp _ rev189_plane14_mem) (hp _ rev189_plane37_mem)
  exact (rev189_plane14.combine rev189_plane37 1393416000000 1393416000000).xBoundCheck_sound rev189_s3_lr.nx rev189_s3_lr.dx false (by decide) p hc
theorem rev189_hull (p : Point) (hp : p∈IntegerCarrier rev189_planes) :
    p∈rationalHull (fractionRow189.map FractionPoint.rational) := by
  have hxlo := rev189_bound0_lo p hp
  have hxhi := rev189_bound0_hi p hp
  by_cases h0 : p.1≤rev189_s0_lr.real.1
  · exact rev189_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev189_s1_lr.real.1
  · exact rev189_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev189_s2_lr.real.1
  · exact rev189_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev189_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull189 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,10,4,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow189 := by
  rw [← fractionRow189_correct]
  exact rev189_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull189
