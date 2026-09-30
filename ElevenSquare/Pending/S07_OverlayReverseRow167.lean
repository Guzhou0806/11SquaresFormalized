import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks20
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev167_planes : List IntegerPlane := integerOverlayPlanes ![11,4,10,13]
def rev167_plane10 : IntegerPlane := ⟨(-2093220000000),(-1468788000000),(-2349463273104)⟩
theorem rev167_plane10_mem : rev167_plane10 ∈ rev167_planes := by decide
def rev167_plane11 : IntegerPlane := ⟨(-48252000000),(-2112760000000),(-1031002749085)⟩
theorem rev167_plane11_mem : rev167_plane11 ∈ rev167_planes := by decide
def rev167_plane57 : IntegerPlane := ⟨1393416000000,2099728000000,2133599860516⟩
theorem rev167_plane57_mem : rev167_plane57 ∈ rev167_planes := by decide
def rev167_plane58 : IntegerPlane := ⟨2139440000000,16372000000,1762107152575⟩
theorem rev167_plane58_mem : rev167_plane58 ∈ rev167_planes := by decide
def rev167_plane74 : IntegerPlane := ⟨(-1393416000000),2099728000000,(-33871860516)⟩
theorem rev167_plane74_mem : rev167_plane74 ∈ rev167_planes := by decide
def rev167_vertex0 : FractionPoint := fractionRow167[0]!
theorem rev167_vertex0_mem : rev167_vertex0∈fractionRow167 := by decide
def rev167_vertex1 : FractionPoint := fractionRow167[1]!
theorem rev167_vertex1_mem : rev167_vertex1∈fractionRow167 := by decide
def rev167_vertex2 : FractionPoint := fractionRow167[2]!
theorem rev167_vertex2_mem : rev167_vertex2∈fractionRow167 := by decide
def rev167_vertex3 : FractionPoint := fractionRow167[3]!
theorem rev167_vertex3_mem : rev167_vertex3∈fractionRow167 := by decide
def rev167_vertex4 : FractionPoint := fractionRow167[4]!
theorem rev167_vertex4_mem : rev167_vertex4∈fractionRow167 := by decide
def rev167_s0_ll : FractionPoint := ⟨20762435007382043,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev167_s0_ll_mem : rev167_s0_ll.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane10 rev167_vertex0 rev167_vertex1 rev167_s0_ll
    rev167_vertex0_mem rev167_vertex1_mem (by decide)
def rev167_s0_lr : FractionPoint := ⟨270933965129,348354000000,6981125959765151,14212727082000000⟩
theorem rev167_s0_lr_mem : rev167_s0_lr.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane10 rev167_vertex0 rev167_vertex1 rev167_s0_lr
    rev167_vertex0_mem rev167_vertex1_mem (by decide)
def rev167_s0_ul : FractionPoint := ⟨20762435007382043,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev167_s0_ul_mem : rev167_s0_ul.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane74 rev167_vertex0 rev167_vertex4 rev167_s0_ul
    rev167_vertex0_mem rev167_vertex4_mem (by decide)
def rev167_s0_ur : FractionPoint := ⟨270933965129,348354000000,1,2⟩
theorem rev167_s0_ur_mem : rev167_s0_ur.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane74 rev167_vertex0 rev167_vertex4 rev167_s0_ur
    rev167_vertex0_mem rev167_vertex4_mem (by decide)
theorem rev167_slab0 (p : Point) (hp : p∈IntegerCarrier rev167_planes)
    (hx0 : rev167_s0_ll.real.1≤p.1) (hx1 : p.1≤rev167_s0_lr.real.1) :
    p∈rationalHull (fractionRow167.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev167_plane10 rev167_plane74 rev167_s0_ll rev167_s0_lr rev167_s0_ul rev167_s0_ur
    (by decide) rev167_s0_ll_mem rev167_s0_lr_mem rev167_s0_ul_mem rev167_s0_ur_mem p
    (hp _ rev167_plane10_mem) (hp _ rev167_plane74_mem) hx0 hx1
def rev167_s1_ll : FractionPoint := ⟨270933965129,348354000000,6981125959765151,14212727082000000⟩
theorem rev167_s1_ll_mem : rev167_s1_ll.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane10 rev167_vertex0 rev167_vertex1 rev167_s1_ll
    rev167_vertex0_mem rev167_vertex1_mem (by decide)
def rev167_s1_lr : FractionPoint := ⟨57492125984335801,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev167_s1_lr_mem : rev167_s1_lr.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane10 rev167_vertex0 rev167_vertex1 rev167_s1_lr
    rev167_vertex0_mem rev167_vertex1_mem (by decide)
def rev167_s1_ul : FractionPoint := ⟨270933965129,348354000000,1,2⟩
theorem rev167_s1_ul_mem : rev167_s1_ul.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane57 rev167_vertex4 rev167_vertex3 rev167_s1_ul
    rev167_vertex4_mem rev167_vertex3_mem (by decide)
def rev167_s1_ur : FractionPoint := ⟨57492125984335801,72526658810400000,5182807007011924166941,10575434461850248000000⟩
theorem rev167_s1_ur_mem : rev167_s1_ur.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane57 rev167_vertex4 rev167_vertex3 rev167_s1_ur
    rev167_vertex4_mem rev167_vertex3_mem (by decide)
theorem rev167_slab1 (p : Point) (hp : p∈IntegerCarrier rev167_planes)
    (hx0 : rev167_s1_ll.real.1≤p.1) (hx1 : p.1≤rev167_s1_lr.real.1) :
    p∈rationalHull (fractionRow167.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev167_plane10 rev167_plane57 rev167_s1_ll rev167_s1_lr rev167_s1_ul rev167_s1_ur
    (by decide) rev167_s1_ll_mem rev167_s1_lr_mem rev167_s1_ul_mem rev167_s1_ur_mem p
    (hp _ rev167_plane10_mem) (hp _ rev167_plane57_mem) hx0 hx1
def rev167_s2_ll : FractionPoint := ⟨57492125984335801,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev167_s2_ll_mem : rev167_s2_ll.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane11 rev167_vertex1 rev167_vertex2 rev167_s2_ll
    rev167_vertex1_mem rev167_vertex2_mem (by decide)
def rev167_s2_lr : FractionPoint := ⟨114531700948300989,139669658299000000,138473418035874165585187,295088467267795240000000⟩
theorem rev167_s2_lr_mem : rev167_s2_lr.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane11 rev167_vertex1 rev167_vertex2 rev167_s2_lr
    rev167_vertex1_mem rev167_vertex2_mem (by decide)
def rev167_s2_ul : FractionPoint := ⟨57492125984335801,72526658810400000,5182807007011924166941,10575434461850248000000⟩
theorem rev167_s2_ul_mem : rev167_s2_ul.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane57 rev167_vertex4 rev167_vertex3 rev167_s2_ul
    rev167_vertex4_mem rev167_vertex3_mem (by decide)
def rev167_s2_ur : FractionPoint := ⟨114531700948300989,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev167_s2_ur_mem : rev167_s2_ur.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane57 rev167_vertex4 rev167_vertex3 rev167_s2_ur
    rev167_vertex4_mem rev167_vertex3_mem (by decide)
theorem rev167_slab2 (p : Point) (hp : p∈IntegerCarrier rev167_planes)
    (hx0 : rev167_s2_ll.real.1≤p.1) (hx1 : p.1≤rev167_s2_lr.real.1) :
    p∈rationalHull (fractionRow167.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev167_plane11 rev167_plane57 rev167_s2_ll rev167_s2_lr rev167_s2_ul rev167_s2_ur
    (by decide) rev167_s2_ll_mem rev167_s2_lr_mem rev167_s2_ul_mem rev167_s2_ur_mem p
    (hp _ rev167_plane11_mem) (hp _ rev167_plane57_mem) hx0 hx1
def rev167_s3_ll : FractionPoint := ⟨114531700948300989,139669658299000000,138473418035874165585187,295088467267795240000000⟩
theorem rev167_s3_ll_mem : rev167_s3_ll.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane11 rev167_vertex1 rev167_vertex2 rev167_s3_ll
    rev167_vertex1_mem rev167_vertex2_mem (by decide)
def rev167_s3_lr : FractionPoint := ⟨185301496533316869,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev167_s3_lr_mem : rev167_s3_lr.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane11 rev167_vertex1 rev167_vertex2 rev167_s3_lr
    rev167_vertex1_mem rev167_vertex2_mem (by decide)
def rev167_s3_ul : FractionPoint := ⟨114531700948300989,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev167_s3_ul_mem : rev167_s3_ul.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane58 rev167_vertex3 rev167_vertex2 rev167_s3_ul
    rev167_vertex3_mem rev167_vertex2_mem (by decide)
def rev167_s3_ur : FractionPoint := ⟨185301496533316869,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev167_s3_ur_mem : rev167_s3_ur.real ∈ rationalHull (fractionRow167.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow167 rev167_plane58 rev167_vertex3 rev167_vertex2 rev167_s3_ur
    rev167_vertex3_mem rev167_vertex2_mem (by decide)
theorem rev167_slab3 (p : Point) (hp : p∈IntegerCarrier rev167_planes)
    (hx0 : rev167_s3_ll.real.1≤p.1) (hx1 : p.1≤rev167_s3_lr.real.1) :
    p∈rationalHull (fractionRow167.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev167_plane11 rev167_plane58 rev167_s3_ll rev167_s3_lr rev167_s3_ul rev167_s3_ur
    (by decide) rev167_s3_ll_mem rev167_s3_lr_mem rev167_s3_ul_mem rev167_s3_ur_mem p
    (hp _ rev167_plane11_mem) (hp _ rev167_plane58_mem) hx0 hx1
theorem rev167_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev167_planes) : rev167_s0_ll.real.1≤p.1 := by
  have hc := rev167_plane10.combine_sound rev167_plane74 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev167_plane10_mem) (hp _ rev167_plane74_mem)
  exact (rev167_plane10.combine rev167_plane74 2099728000000 1468788000000).xBoundCheck_sound rev167_s0_ll.nx rev167_s0_ll.dx true (by decide) p hc
theorem rev167_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev167_planes) : p.1≤rev167_s3_lr.real.1 := by
  have hc := rev167_plane11.combine_sound rev167_plane58 16372000000 2112760000000 (by decide) (by decide) p
    (hp _ rev167_plane11_mem) (hp _ rev167_plane58_mem)
  exact (rev167_plane11.combine rev167_plane58 16372000000 2112760000000).xBoundCheck_sound rev167_s3_lr.nx rev167_s3_lr.dx false (by decide) p hc
theorem rev167_hull (p : Point) (hp : p∈IntegerCarrier rev167_planes) :
    p∈rationalHull (fractionRow167.map FractionPoint.rational) := by
  have hxlo := rev167_bound0_lo p hp
  have hxhi := rev167_bound0_hi p hp
  by_cases h0 : p.1≤rev167_s0_lr.real.1
  · exact rev167_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev167_s1_lr.real.1
  · exact rev167_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev167_s2_lr.real.1
  · exact rev167_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev167_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull167 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,4,10,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow167 := by
  rw [← fractionRow167_correct]
  exact rev167_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull167
