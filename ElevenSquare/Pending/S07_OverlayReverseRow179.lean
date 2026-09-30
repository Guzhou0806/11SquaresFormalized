import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks22
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev179_planes : List IntegerPlane := integerOverlayPlanes ![11,9,13,10]
def rev179_plane10 : IntegerPlane := ⟨(-2093220000000),(-1468788000000),(-2349463273104)⟩
theorem rev179_plane10_mem : rev179_plane10 ∈ rev179_planes := by decide
def rev179_plane14 : IntegerPlane := ⟨(-2144520000000),699568000000,(-1185942108648)⟩
theorem rev179_plane14_mem : rev179_plane14 ∈ rev179_planes := by decide
def rev179_plane28 : IntegerPlane := ⟨2093220000000,(-1468788000000),880675273104⟩
theorem rev179_plane28_mem : rev179_plane28 ∈ rev179_planes := by decide
def rev179_plane32 : IntegerPlane := ⟨2044968000000,643972000000,1962432524019⟩
theorem rev179_plane32_mem : rev179_plane32 ∈ rev179_planes := by decide
def rev179_plane54 : IntegerPlane := ⟨(-1393416000000),(-2099728000000),(-2133599860516)⟩
theorem rev179_plane54_mem : rev179_plane54 ∈ rev179_planes := by decide
def rev179_vertex0 : FractionPoint := fractionRow179[0]!
theorem rev179_vertex0_mem : rev179_vertex0∈fractionRow179 := by decide
def rev179_vertex1 : FractionPoint := fractionRow179[1]!
theorem rev179_vertex1_mem : rev179_vertex1∈fractionRow179 := by decide
def rev179_vertex2 : FractionPoint := fractionRow179[2]!
theorem rev179_vertex2_mem : rev179_vertex2∈fractionRow179 := by decide
def rev179_vertex3 : FractionPoint := fractionRow179[3]!
theorem rev179_vertex3_mem : rev179_vertex3∈fractionRow179 := by decide
def rev179_vertex4 : FractionPoint := fractionRow179[4]!
theorem rev179_vertex4_mem : rev179_vertex4∈fractionRow179 := by decide
def rev179_s0_ll : FractionPoint := ⟨80699534251423,109987485000000,4061837715759,7332499000000⟩
theorem rev179_s0_ll_mem : rev179_s0_ll.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane10 rev179_vertex1 rev179_vertex2 rev179_s0_ll
    rev179_vertex1_mem rev179_vertex2_mem (by decide)
def rev179_s0_lr : FractionPoint := ⟨1935297561189487,2546743666000000,161039762353681848427,311718877974734000000⟩
theorem rev179_s0_lr_mem : rev179_s0_lr.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane10 rev179_vertex1 rev179_vertex2 rev179_s0_lr
    rev179_vertex1_mem rev179_vertex2_mem (by decide)
def rev179_s0_ul : FractionPoint := ⟨80699534251423,109987485000000,4061837715759,7332499000000⟩
theorem rev179_s0_ul_mem : rev179_s0_ul.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane14 rev179_vertex1 rev179_vertex0 rev179_s0_ul
    rev179_vertex1_mem rev179_vertex0_mem (by decide)
def rev179_s0_ur : FractionPoint := ⟨1935297561189487,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev179_s0_ur_mem : rev179_s0_ur.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane14 rev179_vertex1 rev179_vertex0 rev179_s0_ur
    rev179_vertex1_mem rev179_vertex0_mem (by decide)
theorem rev179_slab0 (p : Point) (hp : p∈IntegerCarrier rev179_planes)
    (hx0 : rev179_s0_ll.real.1≤p.1) (hx1 : p.1≤rev179_s0_lr.real.1) :
    p∈rationalHull (fractionRow179.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev179_plane10 rev179_plane14 rev179_s0_ll rev179_s0_lr rev179_s0_ul rev179_s0_ur
    (by decide) rev179_s0_ll_mem rev179_s0_lr_mem rev179_s0_ul_mem rev179_s0_ur_mem p
    (hp _ rev179_plane10_mem) (hp _ rev179_plane14_mem) hx0 hx1
def rev179_s1_ll : FractionPoint := ⟨1935297561189487,2546743666000000,161039762353681848427,311718877974734000000⟩
theorem rev179_s1_ll_mem : rev179_s1_ll.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane10 rev179_vertex1 rev179_vertex2 rev179_s1_ll
    rev179_vertex1_mem rev179_vertex2_mem (by decide)
def rev179_s1_lr : FractionPoint := ⟨37488082241261273,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev179_s1_lr_mem : rev179_s1_lr.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane10 rev179_vertex1 rev179_vertex2 rev179_s1_lr
    rev179_vertex1_mem rev179_vertex2_mem (by decide)
def rev179_s1_ul : FractionPoint := ⟨1935297561189487,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev179_s1_ul_mem : rev179_s1_ul.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane32 rev179_vertex0 rev179_vertex4 rev179_s1_ul
    rev179_vertex0_mem rev179_vertex4_mem (by decide)
def rev179_s1_ur : FractionPoint := ⟨37488082241261273,48928332174000000,3226103639919213760507,5251412654459188000000⟩
theorem rev179_s1_ur_mem : rev179_s1_ur.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane32 rev179_vertex0 rev179_vertex4 rev179_s1_ur
    rev179_vertex0_mem rev179_vertex4_mem (by decide)
theorem rev179_slab1 (p : Point) (hp : p∈IntegerCarrier rev179_planes)
    (hx0 : rev179_s1_ll.real.1≤p.1) (hx1 : p.1≤rev179_s1_lr.real.1) :
    p∈rationalHull (fractionRow179.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev179_plane10 rev179_plane32 rev179_s1_ll rev179_s1_lr rev179_s1_ul rev179_s1_ur
    (by decide) rev179_s1_ll_mem rev179_s1_lr_mem rev179_s1_ul_mem rev179_s1_ur_mem p
    (hp _ rev179_plane10_mem) (hp _ rev179_plane32_mem) hx0 hx1
def rev179_s2_ll : FractionPoint := ⟨37488082241261273,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev179_s2_ll_mem : rev179_s2_ll.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane54 rev179_vertex2 rev179_vertex3 rev179_s2_ll
    rev179_vertex2_mem rev179_vertex3_mem (by decide)
def rev179_s2_lr : FractionPoint := ⟨20762435007382043,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev179_s2_lr_mem : rev179_s2_lr.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane54 rev179_vertex2 rev179_vertex3 rev179_s2_lr
    rev179_vertex2_mem rev179_vertex3_mem (by decide)
def rev179_s2_ul : FractionPoint := ⟨37488082241261273,48928332174000000,3226103639919213760507,5251412654459188000000⟩
theorem rev179_s2_ul_mem : rev179_s2_ul.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane32 rev179_vertex0 rev179_vertex4 rev179_s2_ul
    rev179_vertex0_mem rev179_vertex4_mem (by decide)
def rev179_s2_ur : FractionPoint := ⟨20762435007382043,26840938933200000,8512513621286232939089,14404010938908892000000⟩
theorem rev179_s2_ur_mem : rev179_s2_ur.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane32 rev179_vertex0 rev179_vertex4 rev179_s2_ur
    rev179_vertex0_mem rev179_vertex4_mem (by decide)
theorem rev179_slab2 (p : Point) (hp : p∈IntegerCarrier rev179_planes)
    (hx0 : rev179_s2_ll.real.1≤p.1) (hx1 : p.1≤rev179_s2_lr.real.1) :
    p∈rationalHull (fractionRow179.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev179_plane54 rev179_plane32 rev179_s2_ll rev179_s2_lr rev179_s2_ul rev179_s2_ur
    (by decide) rev179_s2_ll_mem rev179_s2_lr_mem rev179_s2_ul_mem rev179_s2_ur_mem p
    (hp _ rev179_plane54_mem) (hp _ rev179_plane32_mem) hx0 hx1
def rev179_s3_ll : FractionPoint := ⟨20762435007382043,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev179_s3_ll_mem : rev179_s3_ll.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane28 rev179_vertex3 rev179_vertex4 rev179_s3_ll
    rev179_vertex3_mem rev179_vertex4_mem (by decide)
def rev179_s3_lr : FractionPoint := ⟨57492125984335801,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev179_s3_lr_mem : rev179_s3_lr.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane28 rev179_vertex3 rev179_vertex4 rev179_s3_lr
    rev179_vertex3_mem rev179_vertex4_mem (by decide)
def rev179_s3_ul : FractionPoint := ⟨20762435007382043,26840938933200000,8512513621286232939089,14404010938908892000000⟩
theorem rev179_s3_ul_mem : rev179_s3_ul.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane32 rev179_vertex0 rev179_vertex4 rev179_s3_ul
    rev179_vertex0_mem rev179_vertex4_mem (by decide)
def rev179_s3_ur : FractionPoint := ⟨57492125984335801,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev179_s3_ur_mem : rev179_s3_ur.real ∈ rationalHull (fractionRow179.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow179 rev179_plane32 rev179_vertex0 rev179_vertex4 rev179_s3_ur
    rev179_vertex0_mem rev179_vertex4_mem (by decide)
theorem rev179_slab3 (p : Point) (hp : p∈IntegerCarrier rev179_planes)
    (hx0 : rev179_s3_ll.real.1≤p.1) (hx1 : p.1≤rev179_s3_lr.real.1) :
    p∈rationalHull (fractionRow179.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev179_plane28 rev179_plane32 rev179_s3_ll rev179_s3_lr rev179_s3_ul rev179_s3_ur
    (by decide) rev179_s3_ll_mem rev179_s3_lr_mem rev179_s3_ul_mem rev179_s3_ur_mem p
    (hp _ rev179_plane28_mem) (hp _ rev179_plane32_mem) hx0 hx1
theorem rev179_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev179_planes) : rev179_s0_ll.real.1≤p.1 := by
  have hc := rev179_plane10.combine_sound rev179_plane14 699568000000 1468788000000 (by decide) (by decide) p
    (hp _ rev179_plane10_mem) (hp _ rev179_plane14_mem)
  exact (rev179_plane10.combine rev179_plane14 699568000000 1468788000000).xBoundCheck_sound rev179_s0_ll.nx rev179_s0_ll.dx true (by decide) p hc
theorem rev179_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev179_planes) : p.1≤rev179_s3_lr.real.1 := by
  have hc := rev179_plane28.combine_sound rev179_plane32 643972000000 1468788000000 (by decide) (by decide) p
    (hp _ rev179_plane28_mem) (hp _ rev179_plane32_mem)
  exact (rev179_plane28.combine rev179_plane32 643972000000 1468788000000).xBoundCheck_sound rev179_s3_lr.nx rev179_s3_lr.dx false (by decide) p hc
theorem rev179_hull (p : Point) (hp : p∈IntegerCarrier rev179_planes) :
    p∈rationalHull (fractionRow179.map FractionPoint.rational) := by
  have hxlo := rev179_bound0_lo p hp
  have hxhi := rev179_bound0_hi p hp
  by_cases h0 : p.1≤rev179_s0_lr.real.1
  · exact rev179_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev179_s1_lr.real.1
  · exact rev179_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev179_s2_lr.real.1
  · exact rev179_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev179_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull179 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,9,13,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow179 := by
  rw [← fractionRow179_correct]
  exact rev179_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull179
