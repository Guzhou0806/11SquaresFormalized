import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks25
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev202_planes : List IntegerPlane := integerOverlayPlanes ![14,13,4,11]
def rev202_plane14 : IntegerPlane := ⟨16372000000,(-2139440000000),(-1745735152575)⟩
theorem rev202_plane14_mem : rev202_plane14 ∈ rev202_planes := by decide
def rev202_plane17 : IntegerPlane := ⟨(-2083356000000),(-746024000000),(-1711863292059)⟩
theorem rev202_plane17_mem : rev202_plane17 ∈ rev202_planes := by decide
def rev202_plane38 : IntegerPlane := ⟨(-2083356000000),746024000000,(-371492707941)⟩
theorem rev202_plane38_mem : rev202_plane38 ∈ rev202_planes := by decide
def rev202_plane52 : IntegerPlane := ⟨2112760000000,(-48252000000),1081757250915⟩
theorem rev202_plane52_mem : rev202_plane52 ∈ rev202_planes := by decide
def rev202_vertex0 : FractionPoint := fractionRow202[0]!
theorem rev202_vertex0_mem : rev202_vertex0∈fractionRow202 := by decide
def rev202_vertex1 : FractionPoint := fractionRow202[1]!
theorem rev202_vertex1_mem : rev202_vertex1∈fractionRow202 := by decide
def rev202_vertex2 : FractionPoint := fractionRow202[2]!
theorem rev202_vertex2_mem : rev202_vertex2∈fractionRow202 := by decide
def rev202_vertex3 : FractionPoint := fractionRow202[3]!
theorem rev202_vertex3_mem : rev202_vertex3∈fractionRow202 := by decide
def rev202_s0_ll : FractionPoint := ⟨1,2,670185292059,746024000000⟩
theorem rev202_s0_ll_mem : rev202_s0_ll.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane17 rev202_vertex1 rev202_vertex2 rev202_s0_ll
    rev202_vertex1_mem rev202_vertex2_mem (by decide)
def rev202_s0_lr : FractionPoint := ⟨59001712002452379,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev202_s0_lr_mem : rev202_s0_lr.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane17 rev202_vertex1 rev202_vertex2 rev202_s0_lr
    rev202_vertex1_mem rev202_vertex2_mem (by decide)
def rev202_s0_ul : FractionPoint := ⟨1,2,670185292059,746024000000⟩
theorem rev202_s0_ul_mem : rev202_s0_ul.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane38 rev202_vertex1 rev202_vertex0 rev202_s0_ul
    rev202_vertex1_mem rev202_vertex0_mem (by decide)
def rev202_s0_ur : FractionPoint := ⟨59001712002452379,111735726639200000,50882851904768399638773,52098458581426588000000⟩
theorem rev202_s0_ur_mem : rev202_s0_ur.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane38 rev202_vertex1 rev202_vertex0 rev202_s0_ur
    rev202_vertex1_mem rev202_vertex0_mem (by decide)
theorem rev202_slab0 (p : Point) (hp : p∈IntegerCarrier rev202_planes)
    (hx0 : rev202_s0_ll.real.1≤p.1) (hx1 : p.1≤rev202_s0_lr.real.1) :
    p∈rationalHull (fractionRow202.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev202_plane17 rev202_plane38 rev202_s0_ll rev202_s0_lr rev202_s0_ul rev202_s0_ur
    (by decide) rev202_s0_ll_mem rev202_s0_lr_mem rev202_s0_ul_mem rev202_s0_ur_mem p
    (hp _ rev202_plane17_mem) (hp _ rev202_plane38_mem) hx0 hx1
def rev202_s1_ll : FractionPoint := ⟨59001712002452379,111735726639200000,114531700948300989,139669658299000000⟩
theorem rev202_s1_ll_mem : rev202_s1_ll.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane14 rev202_vertex2 rev202_vertex3 rev202_s1_ll
    rev202_vertex2_mem rev202_vertex3_mem (by decide)
def rev202_s1_lr : FractionPoint := ⟨4797179890959273,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev202_s1_lr_mem : rev202_s1_lr.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane14 rev202_vertex2 rev202_vertex3 rev202_s1_lr
    rev202_vertex2_mem rev202_vertex3_mem (by decide)
def rev202_s1_ul : FractionPoint := ⟨59001712002452379,111735726639200000,50882851904768399638773,52098458581426588000000⟩
theorem rev202_s1_ul_mem : rev202_s1_ul.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane38 rev202_vertex1 rev202_vertex0 rev202_s1_ul
    rev202_vertex1_mem rev202_vertex0_mem (by decide)
def rev202_s1_ur : FractionPoint := ⟨4797179890959273,9038666545312000,103694293715869826585397,105360346418747492000000⟩
theorem rev202_s1_ur_mem : rev202_s1_ur.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane38 rev202_vertex1 rev202_vertex0 rev202_s1_ur
    rev202_vertex1_mem rev202_vertex0_mem (by decide)
theorem rev202_slab1 (p : Point) (hp : p∈IntegerCarrier rev202_planes)
    (hx0 : rev202_s1_ll.real.1≤p.1) (hx1 : p.1≤rev202_s1_lr.real.1) :
    p∈rationalHull (fractionRow202.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev202_plane14 rev202_plane38 rev202_s1_ll rev202_s1_lr rev202_s1_ul rev202_s1_ur
    (by decide) rev202_s1_ll_mem rev202_s1_lr_mem rev202_s1_ul_mem rev202_s1_ur_mem p
    (hp _ rev202_plane14_mem) (hp _ rev202_plane38_mem) hx0 hx1
def rev202_s2_ll : FractionPoint := ⟨4797179890959273,9038666545312000,185301496533316869,225966663632800000⟩
theorem rev202_s2_ll_mem : rev202_s2_ll.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane52 rev202_vertex3 rev202_vertex0 rev202_s2_ll
    rev202_vertex3_mem rev202_vertex0_mem (by decide)
def rev202_s2_lr : FractionPoint := ⟨197272901303260707,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev202_s2_lr_mem : rev202_s2_lr.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane52 rev202_vertex3 rev202_vertex0 rev202_s2_lr
    rev202_vertex3_mem rev202_vertex0_mem (by decide)
def rev202_s2_ul : FractionPoint := ⟨4797179890959273,9038666545312000,103694293715869826585397,105360346418747492000000⟩
theorem rev202_s2_ul_mem : rev202_s2_ul.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane38 rev202_vertex1 rev202_vertex0 rev202_s2_ul
    rev202_vertex1_mem rev202_vertex0_mem (by decide)
def rev202_s2_ur : FractionPoint := ⟨197272901303260707,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev202_s2_ur_mem : rev202_s2_ur.real ∈ rationalHull (fractionRow202.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow202 rev202_plane38 rev202_vertex1 rev202_vertex0 rev202_s2_ur
    rev202_vertex1_mem rev202_vertex0_mem (by decide)
theorem rev202_slab2 (p : Point) (hp : p∈IntegerCarrier rev202_planes)
    (hx0 : rev202_s2_ll.real.1≤p.1) (hx1 : p.1≤rev202_s2_lr.real.1) :
    p∈rationalHull (fractionRow202.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev202_plane52 rev202_plane38 rev202_s2_ll rev202_s2_lr rev202_s2_ul rev202_s2_ur
    (by decide) rev202_s2_ll_mem rev202_s2_lr_mem rev202_s2_ul_mem rev202_s2_ur_mem p
    (hp _ rev202_plane52_mem) (hp _ rev202_plane38_mem) hx0 hx1
theorem rev202_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev202_planes) : rev202_s0_ll.real.1≤p.1 := by
  have hc := rev202_plane17.combine_sound rev202_plane38 746024000000 746024000000 (by decide) (by decide) p
    (hp _ rev202_plane17_mem) (hp _ rev202_plane38_mem)
  exact (rev202_plane17.combine rev202_plane38 746024000000 746024000000).xBoundCheck_sound rev202_s0_ll.nx rev202_s0_ll.dx true (by decide) p hc
theorem rev202_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev202_planes) : p.1≤rev202_s2_lr.real.1 := by
  have hc := rev202_plane38.combine_sound rev202_plane52 48252000000 746024000000 (by decide) (by decide) p
    (hp _ rev202_plane38_mem) (hp _ rev202_plane52_mem)
  exact (rev202_plane38.combine rev202_plane52 48252000000 746024000000).xBoundCheck_sound rev202_s2_lr.nx rev202_s2_lr.dx false (by decide) p hc
theorem rev202_hull (p : Point) (hp : p∈IntegerCarrier rev202_planes) :
    p∈rationalHull (fractionRow202.map FractionPoint.rational) := by
  have hxlo := rev202_bound0_lo p hp
  have hxhi := rev202_bound0_hi p hp
  by_cases h0 : p.1≤rev202_s0_lr.real.1
  · exact rev202_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev202_s1_lr.real.1
  · exact rev202_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev202_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull202 (p : Point)
    (hp : ∀ g, ClosedCell ((![14,13,4,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow202 := by
  rw [← fractionRow202_correct]
  exact rev202_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull202
