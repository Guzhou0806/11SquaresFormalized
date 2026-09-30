import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks20
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev164_planes : List IntegerPlane := integerOverlayPlanes ![10,13,9,11]
def rev164_plane34 : IntegerPlane := ⟨(-2099728000000),(-1393416000000),(-2133599860516)⟩
theorem rev164_plane34_mem : rev164_plane34 ∈ rev164_planes := by decide
def rev164_plane48 : IntegerPlane := ⟨(-1468788000000),2093220000000,880675273104⟩
theorem rev164_plane48_mem : rev164_plane48 ∈ rev164_planes := by decide
def rev164_plane52 : IntegerPlane := ⟨643972000000,2044968000000,1962432524019⟩
theorem rev164_plane52_mem : rev164_plane52 ∈ rev164_planes := by decide
def rev164_plane70 : IntegerPlane := ⟨(-1468788000000),(-2093220000000),(-2349463273104)⟩
theorem rev164_plane70_mem : rev164_plane70 ∈ rev164_planes := by decide
def rev164_plane74 : IntegerPlane := ⟨699568000000,(-2144520000000),(-1185942108648)⟩
theorem rev164_plane74_mem : rev164_plane74 ∈ rev164_planes := by decide
def rev164_vertex0 : FractionPoint := fractionRow164[0]!
theorem rev164_vertex0_mem : rev164_vertex0∈fractionRow164 := by decide
def rev164_vertex1 : FractionPoint := fractionRow164[1]!
theorem rev164_vertex1_mem : rev164_vertex1∈fractionRow164 := by decide
def rev164_vertex2 : FractionPoint := fractionRow164[2]!
theorem rev164_vertex2_mem : rev164_vertex2∈fractionRow164 := by decide
def rev164_vertex3 : FractionPoint := fractionRow164[3]!
theorem rev164_vertex3_mem : rev164_vertex3∈fractionRow164 := by decide
def rev164_vertex4 : FractionPoint := fractionRow164[4]!
theorem rev164_vertex4_mem : rev164_vertex4∈fractionRow164 := by decide
def rev164_s0_ll : FractionPoint := ⟨22492686692234849,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev164_s0_ll_mem : rev164_s0_ll.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane34 rev164_vertex0 rev164_vertex1 rev164_s0_ll
    rev164_vertex0_mem rev164_vertex1_mem (by decide)
def rev164_s0_lr : FractionPoint := ⟨8279959610234849,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev164_s0_lr_mem : rev164_s0_lr.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane34 rev164_vertex0 rev164_vertex1 rev164_s0_lr
    rev164_vertex0_mem rev164_vertex1_mem (by decide)
def rev164_s0_ul : FractionPoint := ⟨22492686692234849,44734898222000000,20762435007382043,26840938933200000⟩
theorem rev164_s0_ul_mem : rev164_s0_ul.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane48 rev164_vertex0 rev164_vertex4 rev164_s0_ul
    rev164_vertex0_mem rev164_vertex4_mem (by decide)
def rev164_s0_ur : FractionPoint := ⟨8279959610234849,16309444058000000,2210402451329265284087,2844937874257230000000⟩
theorem rev164_s0_ur_mem : rev164_s0_ur.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane48 rev164_vertex0 rev164_vertex4 rev164_s0_ur
    rev164_vertex0_mem rev164_vertex4_mem (by decide)
theorem rev164_slab0 (p : Point) (hp : p∈IntegerCarrier rev164_planes)
    (hx0 : rev164_s0_ll.real.1≤p.1) (hx1 : p.1≤rev164_s0_lr.real.1) :
    p∈rationalHull (fractionRow164.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev164_plane34 rev164_plane48 rev164_s0_ll rev164_s0_lr rev164_s0_ul rev164_s0_ur
    (by decide) rev164_s0_ll_mem rev164_s0_lr_mem rev164_s0_ul_mem rev164_s0_ur_mem p
    (hp _ rev164_plane34_mem) (hp _ rev164_plane48_mem) hx0 hx1
def rev164_s1_ll : FractionPoint := ⟨8279959610234849,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev164_s1_ll_mem : rev164_s1_ll.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane70 rev164_vertex1 rev164_vertex2 rev164_s1_ll
    rev164_vertex1_mem rev164_vertex2_mem (by decide)
def rev164_s1_lr : FractionPoint := ⟨64079173778836403,120877764684000000,15823262263641347964131,21085312882653540000000⟩
theorem rev164_s1_lr_mem : rev164_s1_lr.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane70 rev164_vertex1 rev164_vertex2 rev164_s1_lr
    rev164_vertex1_mem rev164_vertex2_mem (by decide)
def rev164_s1_ul : FractionPoint := ⟨8279959610234849,16309444058000000,2210402451329265284087,2844937874257230000000⟩
theorem rev164_s1_ul_mem : rev164_s1_ul.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane48 rev164_vertex0 rev164_vertex4 rev164_s1_ul
    rev164_vertex0_mem rev164_vertex4_mem (by decide)
def rev164_s1_ur : FractionPoint := ⟨64079173778836403,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev164_s1_ur_mem : rev164_s1_ur.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane48 rev164_vertex0 rev164_vertex4 rev164_s1_ur
    rev164_vertex0_mem rev164_vertex4_mem (by decide)
theorem rev164_slab1 (p : Point) (hp : p∈IntegerCarrier rev164_planes)
    (hx0 : rev164_s1_ll.real.1≤p.1) (hx1 : p.1≤rev164_s1_lr.real.1) :
    p∈rationalHull (fractionRow164.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev164_plane70 rev164_plane48 rev164_s1_ll rev164_s1_lr rev164_s1_ul rev164_s1_ur
    (by decide) rev164_s1_ll_mem rev164_s1_lr_mem rev164_s1_ul_mem rev164_s1_ur_mem p
    (hp _ rev164_plane70_mem) (hp _ rev164_plane48_mem) hx0 hx1
def rev164_s2_ll : FractionPoint := ⟨64079173778836403,120877764684000000,15823262263641347964131,21085312882653540000000⟩
theorem rev164_s2_ll_mem : rev164_s2_ll.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane70 rev164_vertex1 rev164_vertex2 rev164_s2_ll
    rev164_vertex1_mem rev164_vertex2_mem (by decide)
def rev164_s2_lr : FractionPoint := ⟨4061837715759,7332499000000,80699534251423,109987485000000⟩
theorem rev164_s2_lr_mem : rev164_s2_lr.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane70 rev164_vertex1 rev164_vertex2 rev164_s2_lr
    rev164_vertex1_mem rev164_vertex2_mem (by decide)
def rev164_s2_ul : FractionPoint := ⟨64079173778836403,120877764684000000,57492125984335801,72526658810400000⟩
theorem rev164_s2_ul_mem : rev164_s2_ul.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane52 rev164_vertex4 rev164_vertex3 rev164_s2_ul
    rev164_vertex4_mem rev164_vertex3_mem (by decide)
def rev164_s2_ur : FractionPoint := ⟨4061837715759,7332499000000,3924608254148012911,4998241938344000000⟩
theorem rev164_s2_ur_mem : rev164_s2_ur.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane52 rev164_vertex4 rev164_vertex3 rev164_s2_ur
    rev164_vertex4_mem rev164_vertex3_mem (by decide)
theorem rev164_slab2 (p : Point) (hp : p∈IntegerCarrier rev164_planes)
    (hx0 : rev164_s2_ll.real.1≤p.1) (hx1 : p.1≤rev164_s2_lr.real.1) :
    p∈rationalHull (fractionRow164.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev164_plane70 rev164_plane52 rev164_s2_ll rev164_s2_lr rev164_s2_ul rev164_s2_ur
    (by decide) rev164_s2_ll_mem rev164_s2_lr_mem rev164_s2_ul_mem rev164_s2_ur_mem p
    (hp _ rev164_plane70_mem) (hp _ rev164_plane52_mem) hx0 hx1
def rev164_s3_ll : FractionPoint := ⟨4061837715759,7332499000000,80699534251423,109987485000000⟩
theorem rev164_s3_ll_mem : rev164_s3_ll.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane74 rev164_vertex2 rev164_vertex3 rev164_s3_ll
    rev164_vertex2_mem rev164_vertex3_mem (by decide)
def rev164_s3_lr : FractionPoint := ⟨3230547344875983,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev164_s3_lr_mem : rev164_s3_lr.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane74 rev164_vertex2 rev164_vertex3 rev164_s3_lr
    rev164_vertex2_mem rev164_vertex3_mem (by decide)
def rev164_s3_ul : FractionPoint := ⟨4061837715759,7332499000000,3924608254148012911,4998241938344000000⟩
theorem rev164_s3_ul_mem : rev164_s3_ul.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane52 rev164_vertex4 rev164_vertex3 rev164_s3_ul
    rev164_vertex4_mem rev164_vertex3_mem (by decide)
def rev164_s3_ur : FractionPoint := ⟨3230547344875983,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev164_s3_ur_mem : rev164_s3_ur.real ∈ rationalHull (fractionRow164.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow164 rev164_plane52 rev164_vertex4 rev164_vertex3 rev164_s3_ur
    rev164_vertex4_mem rev164_vertex3_mem (by decide)
theorem rev164_slab3 (p : Point) (hp : p∈IntegerCarrier rev164_planes)
    (hx0 : rev164_s3_ll.real.1≤p.1) (hx1 : p.1≤rev164_s3_lr.real.1) :
    p∈rationalHull (fractionRow164.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev164_plane74 rev164_plane52 rev164_s3_ll rev164_s3_lr rev164_s3_ul rev164_s3_ur
    (by decide) rev164_s3_ll_mem rev164_s3_lr_mem rev164_s3_ul_mem rev164_s3_ur_mem p
    (hp _ rev164_plane74_mem) (hp _ rev164_plane52_mem) hx0 hx1
theorem rev164_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev164_planes) : rev164_s0_ll.real.1≤p.1 := by
  have hc := rev164_plane34.combine_sound rev164_plane48 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev164_plane34_mem) (hp _ rev164_plane48_mem)
  exact (rev164_plane34.combine rev164_plane48 2093220000000 1393416000000).xBoundCheck_sound rev164_s0_ll.nx rev164_s0_ll.dx true (by decide) p hc
theorem rev164_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev164_planes) : p.1≤rev164_s3_lr.real.1 := by
  have hc := rev164_plane52.combine_sound rev164_plane74 2144520000000 2044968000000 (by decide) (by decide) p
    (hp _ rev164_plane52_mem) (hp _ rev164_plane74_mem)
  exact (rev164_plane52.combine rev164_plane74 2144520000000 2044968000000).xBoundCheck_sound rev164_s3_lr.nx rev164_s3_lr.dx false (by decide) p hc
theorem rev164_hull (p : Point) (hp : p∈IntegerCarrier rev164_planes) :
    p∈rationalHull (fractionRow164.map FractionPoint.rational) := by
  have hxlo := rev164_bound0_lo p hp
  have hxhi := rev164_bound0_hi p hp
  by_cases h0 : p.1≤rev164_s0_lr.real.1
  · exact rev164_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev164_s1_lr.real.1
  · exact rev164_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev164_s2_lr.real.1
  · exact rev164_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev164_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull164 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,13,9,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow164 := by
  rw [← fractionRow164_correct]
  exact rev164_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull164
