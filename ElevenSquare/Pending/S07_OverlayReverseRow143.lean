import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks17
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev143_planes : List IntegerPlane := integerOverlayPlanes ![9,11,5,2]
def rev143_plane8 : IntegerPlane := ⟨(-2093220000000),(-1468788000000),(-1212544726896)⟩
theorem rev143_plane8_mem : rev143_plane8 ∈ rev143_planes := by decide
def rev143_plane12 : IntegerPlane := ⟨(-2044968000000),643972000000,(-82535475981)⟩
theorem rev143_plane12_mem : rev143_plane12 ∈ rev143_planes := by decide
def rev143_plane30 : IntegerPlane := ⟨2093220000000,(-1468788000000),(-256243273104)⟩
theorem rev143_plane30_mem : rev143_plane30 ∈ rev143_planes := by decide
def rev143_plane34 : IntegerPlane := ⟨2144520000000,699568000000,958577891352⟩
theorem rev143_plane34_mem : rev143_plane34 ∈ rev143_planes := by decide
def rev143_plane69 : IntegerPlane := ⟨1393416000000,(-2099728000000),(-740183860516)⟩
theorem rev143_plane69_mem : rev143_plane69 ∈ rev143_planes := by decide
def rev143_vertex0 : FractionPoint := fractionRow143[0]!
theorem rev143_vertex0_mem : rev143_vertex0∈fractionRow143 := by decide
def rev143_vertex1 : FractionPoint := fractionRow143[1]!
theorem rev143_vertex1_mem : rev143_vertex1∈fractionRow143 := by decide
def rev143_vertex2 : FractionPoint := fractionRow143[2]!
theorem rev143_vertex2_mem : rev143_vertex2∈fractionRow143 := by decide
def rev143_vertex3 : FractionPoint := fractionRow143[3]!
theorem rev143_vertex3_mem : rev143_vertex3∈fractionRow143 := by decide
def rev143_vertex4 : FractionPoint := fractionRow143[4]!
theorem rev143_vertex4_mem : rev143_vertex4∈fractionRow143 := by decide
def rev143_s0_ll : FractionPoint := ⟨15034532826064199,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev143_s0_ll_mem : rev143_s0_ll.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane8 rev143_vertex1 rev143_vertex2 rev143_s0_ll
    rev143_vertex1_mem rev143_vertex2_mem (by decide)
def rev143_s0_lr : FractionPoint := ⟨6078503925817957,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev143_s0_lr_mem : rev143_s0_lr.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane8 rev143_vertex1 rev143_vertex2 rev143_s0_lr
    rev143_vertex1_mem rev143_vertex2_mem (by decide)
def rev143_s0_ul : FractionPoint := ⟨15034532826064199,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev143_s0_ul_mem : rev143_s0_ul.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane12 rev143_vertex1 rev143_vertex0 rev143_s0_ul
    rev143_vertex1_mem rev143_vertex0_mem (by decide)
def rev143_s0_ur : FractionPoint := ⟨6078503925817957,26840938933200000,8512513621286232939089,14404010938908892000000⟩
theorem rev143_s0_ur_mem : rev143_s0_ur.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane12 rev143_vertex1 rev143_vertex0 rev143_s0_ur
    rev143_vertex1_mem rev143_vertex0_mem (by decide)
theorem rev143_slab0 (p : Point) (hp : p∈IntegerCarrier rev143_planes)
    (hx0 : rev143_s0_ll.real.1≤p.1) (hx1 : p.1≤rev143_s0_lr.real.1) :
    p∈rationalHull (fractionRow143.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev143_plane8 rev143_plane12 rev143_s0_ll rev143_s0_lr rev143_s0_ul rev143_s0_ur
    (by decide) rev143_s0_ll_mem rev143_s0_lr_mem rev143_s0_ul_mem rev143_s0_ur_mem p
    (hp _ rev143_plane8_mem) (hp _ rev143_plane12_mem) hx0 hx1
def rev143_s1_ll : FractionPoint := ⟨6078503925817957,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev143_s1_ll_mem : rev143_s1_ll.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane69 rev143_vertex2 rev143_vertex3 rev143_s1_ll
    rev143_vertex2_mem rev143_vertex3_mem (by decide)
def rev143_s1_lr : FractionPoint := ⟨11440249932738727,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev143_s1_lr_mem : rev143_s1_lr.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane69 rev143_vertex2 rev143_vertex3 rev143_s1_lr
    rev143_vertex2_mem rev143_vertex3_mem (by decide)
def rev143_s1_ul : FractionPoint := ⟨6078503925817957,26840938933200000,8512513621286232939089,14404010938908892000000⟩
theorem rev143_s1_ul_mem : rev143_s1_ul.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane12 rev143_vertex1 rev143_vertex0 rev143_s1_ul
    rev143_vertex1_mem rev143_vertex0_mem (by decide)
def rev143_s1_ur : FractionPoint := ⟨11440249932738727,48928332174000000,3226103639919213760507,5251412654459188000000⟩
theorem rev143_s1_ur_mem : rev143_s1_ur.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane12 rev143_vertex1 rev143_vertex0 rev143_s1_ur
    rev143_vertex1_mem rev143_vertex0_mem (by decide)
theorem rev143_slab1 (p : Point) (hp : p∈IntegerCarrier rev143_planes)
    (hx0 : rev143_s1_ll.real.1≤p.1) (hx1 : p.1≤rev143_s1_lr.real.1) :
    p∈rationalHull (fractionRow143.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev143_plane69 rev143_plane12 rev143_s1_ll rev143_s1_lr rev143_s1_ul rev143_s1_ur
    (by decide) rev143_s1_ll_mem rev143_s1_lr_mem rev143_s1_ul_mem rev143_s1_ur_mem p
    (hp _ rev143_plane69_mem) (hp _ rev143_plane12_mem) hx0 hx1
def rev143_s2_ll : FractionPoint := ⟨11440249932738727,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev143_s2_ll_mem : rev143_s2_ll.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane30 rev143_vertex3 rev143_vertex4 rev143_s2_ll
    rev143_vertex3_mem rev143_vertex4_mem (by decide)
def rev143_s2_lr : FractionPoint := ⟨611446104810513,2546743666000000,161039762353681848427,311718877974734000000⟩
theorem rev143_s2_lr_mem : rev143_s2_lr.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane30 rev143_vertex3 rev143_vertex4 rev143_s2_lr
    rev143_vertex3_mem rev143_vertex4_mem (by decide)
def rev143_s2_ul : FractionPoint := ⟨11440249932738727,48928332174000000,3226103639919213760507,5251412654459188000000⟩
theorem rev143_s2_ul_mem : rev143_s2_ul.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane12 rev143_vertex1 rev143_vertex0 rev143_s2_ul
    rev143_vertex1_mem rev143_vertex0_mem (by decide)
def rev143_s2_ur : FractionPoint := ⟨611446104810513,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev143_s2_ur_mem : rev143_s2_ur.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane12 rev143_vertex1 rev143_vertex0 rev143_s2_ur
    rev143_vertex1_mem rev143_vertex0_mem (by decide)
theorem rev143_slab2 (p : Point) (hp : p∈IntegerCarrier rev143_planes)
    (hx0 : rev143_s2_ll.real.1≤p.1) (hx1 : p.1≤rev143_s2_lr.real.1) :
    p∈rationalHull (fractionRow143.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev143_plane30 rev143_plane12 rev143_s2_ll rev143_s2_lr rev143_s2_ul rev143_s2_ur
    (by decide) rev143_s2_ll_mem rev143_s2_lr_mem rev143_s2_ul_mem rev143_s2_ur_mem p
    (hp _ rev143_plane30_mem) (hp _ rev143_plane12_mem) hx0 hx1
def rev143_s3_ll : FractionPoint := ⟨611446104810513,2546743666000000,161039762353681848427,311718877974734000000⟩
theorem rev143_s3_ll_mem : rev143_s3_ll.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane30 rev143_vertex3 rev143_vertex4 rev143_s3_ll
    rev143_vertex3_mem rev143_vertex4_mem (by decide)
def rev143_s3_lr : FractionPoint := ⟨29287950748577,109987485000000,4061837715759,7332499000000⟩
theorem rev143_s3_lr_mem : rev143_s3_lr.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane30 rev143_vertex3 rev143_vertex4 rev143_s3_lr
    rev143_vertex3_mem rev143_vertex4_mem (by decide)
def rev143_s3_ul : FractionPoint := ⟨611446104810513,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev143_s3_ul_mem : rev143_s3_ul.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane34 rev143_vertex0 rev143_vertex4 rev143_s3_ul
    rev143_vertex0_mem rev143_vertex4_mem (by decide)
def rev143_s3_ur : FractionPoint := ⟨29287950748577,109987485000000,4061837715759,7332499000000⟩
theorem rev143_s3_ur_mem : rev143_s3_ur.real ∈ rationalHull (fractionRow143.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow143 rev143_plane34 rev143_vertex0 rev143_vertex4 rev143_s3_ur
    rev143_vertex0_mem rev143_vertex4_mem (by decide)
theorem rev143_slab3 (p : Point) (hp : p∈IntegerCarrier rev143_planes)
    (hx0 : rev143_s3_ll.real.1≤p.1) (hx1 : p.1≤rev143_s3_lr.real.1) :
    p∈rationalHull (fractionRow143.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev143_plane30 rev143_plane34 rev143_s3_ll rev143_s3_lr rev143_s3_ul rev143_s3_ur
    (by decide) rev143_s3_ll_mem rev143_s3_lr_mem rev143_s3_ul_mem rev143_s3_ur_mem p
    (hp _ rev143_plane30_mem) (hp _ rev143_plane34_mem) hx0 hx1
theorem rev143_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev143_planes) : rev143_s0_ll.real.1≤p.1 := by
  have hc := rev143_plane8.combine_sound rev143_plane12 643972000000 1468788000000 (by decide) (by decide) p
    (hp _ rev143_plane8_mem) (hp _ rev143_plane12_mem)
  exact (rev143_plane8.combine rev143_plane12 643972000000 1468788000000).xBoundCheck_sound rev143_s0_ll.nx rev143_s0_ll.dx true (by decide) p hc
theorem rev143_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev143_planes) : p.1≤rev143_s3_lr.real.1 := by
  have hc := rev143_plane30.combine_sound rev143_plane34 699568000000 1468788000000 (by decide) (by decide) p
    (hp _ rev143_plane30_mem) (hp _ rev143_plane34_mem)
  exact (rev143_plane30.combine rev143_plane34 699568000000 1468788000000).xBoundCheck_sound rev143_s3_lr.nx rev143_s3_lr.dx false (by decide) p hc
theorem rev143_hull (p : Point) (hp : p∈IntegerCarrier rev143_planes) :
    p∈rationalHull (fractionRow143.map FractionPoint.rational) := by
  have hxlo := rev143_bound0_lo p hp
  have hxhi := rev143_bound0_hi p hp
  by_cases h0 : p.1≤rev143_s0_lr.real.1
  · exact rev143_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev143_s1_lr.real.1
  · exact rev143_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev143_s2_lr.real.1
  · exact rev143_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev143_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull143 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,11,5,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow143 := by
  rw [← fractionRow143_correct]
  exact rev143_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull143
