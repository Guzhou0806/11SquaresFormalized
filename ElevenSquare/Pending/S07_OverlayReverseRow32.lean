import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks4
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev32_planes : List IntegerPlane := integerOverlayPlanes ![2,5,11,9]
def rev32_plane9 : IntegerPlane := ⟨(-2099728000000),1393416000000,(-740183860516)⟩
theorem rev32_plane9_mem : rev32_plane9 ∈ rev32_planes := by decide
def rev32_plane50 : IntegerPlane := ⟨(-1468788000000),2093220000000,(-256243273104)⟩
theorem rev32_plane50_mem : rev32_plane50 ∈ rev32_planes := by decide
def rev32_plane54 : IntegerPlane := ⟨699568000000,2144520000000,958577891352⟩
theorem rev32_plane54_mem : rev32_plane54 ∈ rev32_planes := by decide
def rev32_plane68 : IntegerPlane := ⟨(-1468788000000),(-2093220000000),(-1212544726896)⟩
theorem rev32_plane68_mem : rev32_plane68 ∈ rev32_planes := by decide
def rev32_plane72 : IntegerPlane := ⟨643972000000,(-2044968000000),(-82535475981)⟩
theorem rev32_plane72_mem : rev32_plane72 ∈ rev32_planes := by decide
def rev32_vertex0 : FractionPoint := fractionRow32[0]!
theorem rev32_vertex0_mem : rev32_vertex0∈fractionRow32 := by decide
def rev32_vertex1 : FractionPoint := fractionRow32[1]!
theorem rev32_vertex1_mem : rev32_vertex1∈fractionRow32 := by decide
def rev32_vertex2 : FractionPoint := fractionRow32[2]!
theorem rev32_vertex2_mem : rev32_vertex2∈fractionRow32 := by decide
def rev32_vertex3 : FractionPoint := fractionRow32[3]!
theorem rev32_vertex3_mem : rev32_vertex3∈fractionRow32 := by decide
def rev32_vertex4 : FractionPoint := fractionRow32[4]!
theorem rev32_vertex4_mem : rev32_vertex4∈fractionRow32 := by decide
def rev32_s0_ll : FractionPoint := ⟨22492686692234849,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev32_s0_ll_mem : rev32_s0_ll.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane68 rev32_vertex1 rev32_vertex2 rev32_s0_ll
    rev32_vertex1_mem rev32_vertex2_mem (by decide)
def rev32_s0_lr : FractionPoint := ⟨8279959610234849,16309444058000000,634535422927964715913,2844937874257230000000⟩
theorem rev32_s0_lr_mem : rev32_s0_lr.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane68 rev32_vertex1 rev32_vertex2 rev32_s0_lr
    rev32_vertex1_mem rev32_vertex2_mem (by decide)
def rev32_s0_ul : FractionPoint := ⟨22492686692234849,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev32_s0_ul_mem : rev32_s0_ul.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane9 rev32_vertex1 rev32_vertex0 rev32_s0_ul
    rev32_vertex1_mem rev32_vertex0_mem (by decide)
def rev32_s0_ur : FractionPoint := ⟨8279959610234849,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev32_s0_ur_mem : rev32_s0_ur.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane9 rev32_vertex1 rev32_vertex0 rev32_s0_ur
    rev32_vertex1_mem rev32_vertex0_mem (by decide)
theorem rev32_slab0 (p : Point) (hp : p∈IntegerCarrier rev32_planes)
    (hx0 : rev32_s0_ll.real.1≤p.1) (hx1 : p.1≤rev32_s0_lr.real.1) :
    p∈rationalHull (fractionRow32.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev32_plane68 rev32_plane9 rev32_s0_ll rev32_s0_lr rev32_s0_ul rev32_s0_ur
    (by decide) rev32_s0_ll_mem rev32_s0_lr_mem rev32_s0_ul_mem rev32_s0_ur_mem p
    (hp _ rev32_plane68_mem) (hp _ rev32_plane9_mem) hx0 hx1
def rev32_s1_ll : FractionPoint := ⟨8279959610234849,16309444058000000,634535422927964715913,2844937874257230000000⟩
theorem rev32_s1_ll_mem : rev32_s1_ll.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane68 rev32_vertex1 rev32_vertex2 rev32_s1_ll
    rev32_vertex1_mem rev32_vertex2_mem (by decide)
def rev32_s1_lr : FractionPoint := ⟨64079173778836403,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev32_s1_lr_mem : rev32_s1_lr.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane68 rev32_vertex1 rev32_vertex2 rev32_s1_lr
    rev32_vertex1_mem rev32_vertex2_mem (by decide)
def rev32_s1_ul : FractionPoint := ⟨8279959610234849,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev32_s1_ul_mem : rev32_s1_ul.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane50 rev32_vertex0 rev32_vertex4 rev32_s1_ul
    rev32_vertex0_mem rev32_vertex4_mem (by decide)
def rev32_s1_ur : FractionPoint := ⟨64079173778836403,120877764684000000,5262050619012192035869,21085312882653540000000⟩
theorem rev32_s1_ur_mem : rev32_s1_ur.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane50 rev32_vertex0 rev32_vertex4 rev32_s1_ur
    rev32_vertex0_mem rev32_vertex4_mem (by decide)
theorem rev32_slab1 (p : Point) (hp : p∈IntegerCarrier rev32_planes)
    (hx0 : rev32_s1_ll.real.1≤p.1) (hx1 : p.1≤rev32_s1_lr.real.1) :
    p∈rationalHull (fractionRow32.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev32_plane68 rev32_plane50 rev32_s1_ll rev32_s1_lr rev32_s1_ul rev32_s1_ur
    (by decide) rev32_s1_ll_mem rev32_s1_lr_mem rev32_s1_ul_mem rev32_s1_ur_mem p
    (hp _ rev32_plane68_mem) (hp _ rev32_plane50_mem) hx0 hx1
def rev32_s2_ll : FractionPoint := ⟨64079173778836403,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev32_s2_ll_mem : rev32_s2_ll.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane72 rev32_vertex2 rev32_vertex3 rev32_s2_ll
    rev32_vertex2_mem rev32_vertex3_mem (by decide)
def rev32_s2_lr : FractionPoint := ⟨4061837715759,7332499000000,1073633684195987089,4998241938344000000⟩
theorem rev32_s2_lr_mem : rev32_s2_lr.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane72 rev32_vertex2 rev32_vertex3 rev32_s2_lr
    rev32_vertex2_mem rev32_vertex3_mem (by decide)
def rev32_s2_ul : FractionPoint := ⟨64079173778836403,120877764684000000,5262050619012192035869,21085312882653540000000⟩
theorem rev32_s2_ul_mem : rev32_s2_ul.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane50 rev32_vertex0 rev32_vertex4 rev32_s2_ul
    rev32_vertex0_mem rev32_vertex4_mem (by decide)
def rev32_s2_ur : FractionPoint := ⟨4061837715759,7332499000000,29287950748577,109987485000000⟩
theorem rev32_s2_ur_mem : rev32_s2_ur.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane50 rev32_vertex0 rev32_vertex4 rev32_s2_ur
    rev32_vertex0_mem rev32_vertex4_mem (by decide)
theorem rev32_slab2 (p : Point) (hp : p∈IntegerCarrier rev32_planes)
    (hx0 : rev32_s2_ll.real.1≤p.1) (hx1 : p.1≤rev32_s2_lr.real.1) :
    p∈rationalHull (fractionRow32.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev32_plane72 rev32_plane50 rev32_s2_ll rev32_s2_lr rev32_s2_ul rev32_s2_ur
    (by decide) rev32_s2_ll_mem rev32_s2_lr_mem rev32_s2_ul_mem rev32_s2_ur_mem p
    (hp _ rev32_plane72_mem) (hp _ rev32_plane50_mem) hx0 hx1
def rev32_s3_ll : FractionPoint := ⟨4061837715759,7332499000000,1073633684195987089,4998241938344000000⟩
theorem rev32_s3_ll_mem : rev32_s3_ll.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane72 rev32_vertex2 rev32_vertex3 rev32_s3_ll
    rev32_vertex2_mem rev32_vertex3_mem (by decide)
def rev32_s3_lr : FractionPoint := ⟨3230547344875983,5093487332000000,611446104810513,2546743666000000⟩
theorem rev32_s3_lr_mem : rev32_s3_lr.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane72 rev32_vertex2 rev32_vertex3 rev32_s3_lr
    rev32_vertex2_mem rev32_vertex3_mem (by decide)
def rev32_s3_ul : FractionPoint := ⟨4061837715759,7332499000000,29287950748577,109987485000000⟩
theorem rev32_s3_ul_mem : rev32_s3_ul.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane54 rev32_vertex4 rev32_vertex3 rev32_s3_ul
    rev32_vertex4_mem rev32_vertex3_mem (by decide)
def rev32_s3_ur : FractionPoint := ⟨3230547344875983,5093487332000000,611446104810513,2546743666000000⟩
theorem rev32_s3_ur_mem : rev32_s3_ur.real ∈ rationalHull (fractionRow32.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow32 rev32_plane54 rev32_vertex4 rev32_vertex3 rev32_s3_ur
    rev32_vertex4_mem rev32_vertex3_mem (by decide)
theorem rev32_slab3 (p : Point) (hp : p∈IntegerCarrier rev32_planes)
    (hx0 : rev32_s3_ll.real.1≤p.1) (hx1 : p.1≤rev32_s3_lr.real.1) :
    p∈rationalHull (fractionRow32.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev32_plane72 rev32_plane54 rev32_s3_ll rev32_s3_lr rev32_s3_ul rev32_s3_ur
    (by decide) rev32_s3_ll_mem rev32_s3_lr_mem rev32_s3_ul_mem rev32_s3_ur_mem p
    (hp _ rev32_plane72_mem) (hp _ rev32_plane54_mem) hx0 hx1
theorem rev32_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev32_planes) : rev32_s0_ll.real.1≤p.1 := by
  have hc := rev32_plane9.combine_sound rev32_plane68 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev32_plane9_mem) (hp _ rev32_plane68_mem)
  exact (rev32_plane9.combine rev32_plane68 2093220000000 1393416000000).xBoundCheck_sound rev32_s0_ll.nx rev32_s0_ll.dx true (by decide) p hc
theorem rev32_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev32_planes) : p.1≤rev32_s3_lr.real.1 := by
  have hc := rev32_plane54.combine_sound rev32_plane72 2044968000000 2144520000000 (by decide) (by decide) p
    (hp _ rev32_plane54_mem) (hp _ rev32_plane72_mem)
  exact (rev32_plane54.combine rev32_plane72 2044968000000 2144520000000).xBoundCheck_sound rev32_s3_lr.nx rev32_s3_lr.dx false (by decide) p hc
theorem rev32_hull (p : Point) (hp : p∈IntegerCarrier rev32_planes) :
    p∈rationalHull (fractionRow32.map FractionPoint.rational) := by
  have hxlo := rev32_bound0_lo p hp
  have hxhi := rev32_bound0_hi p hp
  by_cases h0 : p.1≤rev32_s0_lr.real.1
  · exact rev32_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev32_s1_lr.real.1
  · exact rev32_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev32_s2_lr.real.1
  · exact rev32_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev32_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull32 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,5,11,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow32 := by
  rw [← fractionRow32_correct]
  exact rev32_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull32
