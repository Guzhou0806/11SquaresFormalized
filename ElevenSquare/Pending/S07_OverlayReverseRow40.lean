import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks5
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev40_planes : List IntegerPlane := integerOverlayPlanes ![4,6,2,5]
def rev40_plane9 : IntegerPlane := ⟨2144520000000,(-699568000000),259009891352⟩
theorem rev40_plane9_mem : rev40_plane9 ∈ rev40_planes := by decide
def rev40_plane13 : IntegerPlane := ⟨2093220000000,1468788000000,1212544726896⟩
theorem rev40_plane13_mem : rev40_plane13 ∈ rev40_planes := by decide
def rev40_plane31 : IntegerPlane := ⟨(-2044968000000),(-643972000000),(-726507475981)⟩
theorem rev40_plane31_mem : rev40_plane31 ∈ rev40_planes := by decide
def rev40_plane35 : IntegerPlane := ⟨(-2093220000000),1468788000000,256243273104⟩
theorem rev40_plane35_mem : rev40_plane35 ∈ rev40_planes := by decide
def rev40_plane49 : IntegerPlane := ⟨1393416000000,2099728000000,1359544139484⟩
theorem rev40_plane49_mem : rev40_plane49 ∈ rev40_planes := by decide
def rev40_vertex0 : FractionPoint := fractionRow40[0]!
theorem rev40_vertex0_mem : rev40_vertex0∈fractionRow40 := by decide
def rev40_vertex1 : FractionPoint := fractionRow40[1]!
theorem rev40_vertex1_mem : rev40_vertex1∈fractionRow40 := by decide
def rev40_vertex2 : FractionPoint := fractionRow40[2]!
theorem rev40_vertex2_mem : rev40_vertex2∈fractionRow40 := by decide
def rev40_vertex3 : FractionPoint := fractionRow40[3]!
theorem rev40_vertex3_mem : rev40_vertex3∈fractionRow40 := by decide
def rev40_vertex4 : FractionPoint := fractionRow40[4]!
theorem rev40_vertex4_mem : rev40_vertex4∈fractionRow40 := by decide
def rev40_s0_ll : FractionPoint := ⟨15034532826064199,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev40_s0_ll_mem : rev40_s0_ll.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane31 rev40_vertex4 rev40_vertex0 rev40_s0_ll
    rev40_vertex4_mem rev40_vertex0_mem (by decide)
def rev40_s0_lr : FractionPoint := ⟨6078503925817957,26840938933200000,5891497317622659060911,14404010938908892000000⟩
theorem rev40_s0_lr_mem : rev40_s0_lr.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane31 rev40_vertex4 rev40_vertex0 rev40_s0_lr
    rev40_vertex4_mem rev40_vertex0_mem (by decide)
def rev40_s0_ul : FractionPoint := ⟨15034532826064199,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev40_s0_ul_mem : rev40_s0_ul.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane35 rev40_vertex4 rev40_vertex3 rev40_s0_ul
    rev40_vertex4_mem rev40_vertex3_mem (by decide)
def rev40_s0_ur : FractionPoint := ⟨6078503925817957,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev40_s0_ur_mem : rev40_s0_ur.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane35 rev40_vertex4 rev40_vertex3 rev40_s0_ur
    rev40_vertex4_mem rev40_vertex3_mem (by decide)
theorem rev40_slab0 (p : Point) (hp : p∈IntegerCarrier rev40_planes)
    (hx0 : rev40_s0_ll.real.1≤p.1) (hx1 : p.1≤rev40_s0_lr.real.1) :
    p∈rationalHull (fractionRow40.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev40_plane31 rev40_plane35 rev40_s0_ll rev40_s0_lr rev40_s0_ul rev40_s0_ur
    (by decide) rev40_s0_ll_mem rev40_s0_lr_mem rev40_s0_ul_mem rev40_s0_ur_mem p
    (hp _ rev40_plane31_mem) (hp _ rev40_plane35_mem) hx0 hx1
def rev40_s1_ll : FractionPoint := ⟨6078503925817957,26840938933200000,5891497317622659060911,14404010938908892000000⟩
theorem rev40_s1_ll_mem : rev40_s1_ll.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane31 rev40_vertex4 rev40_vertex0 rev40_s1_ll
    rev40_vertex4_mem rev40_vertex0_mem (by decide)
def rev40_s1_lr : FractionPoint := ⟨11440249932738727,48928332174000000,2025309014539974239493,5251412654459188000000⟩
theorem rev40_s1_lr_mem : rev40_s1_lr.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane31 rev40_vertex4 rev40_vertex0 rev40_s1_lr
    rev40_vertex4_mem rev40_vertex0_mem (by decide)
def rev40_s1_ul : FractionPoint := ⟨6078503925817957,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev40_s1_ul_mem : rev40_s1_ul.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane49 rev40_vertex3 rev40_vertex2 rev40_s1_ul
    rev40_vertex3_mem rev40_vertex2_mem (by decide)
def rev40_s1_ur : FractionPoint := ⟨11440249932738727,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev40_s1_ur_mem : rev40_s1_ur.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane49 rev40_vertex3 rev40_vertex2 rev40_s1_ur
    rev40_vertex3_mem rev40_vertex2_mem (by decide)
theorem rev40_slab1 (p : Point) (hp : p∈IntegerCarrier rev40_planes)
    (hx0 : rev40_s1_ll.real.1≤p.1) (hx1 : p.1≤rev40_s1_lr.real.1) :
    p∈rationalHull (fractionRow40.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev40_plane31 rev40_plane49 rev40_s1_ll rev40_s1_lr rev40_s1_ul rev40_s1_ur
    (by decide) rev40_s1_ll_mem rev40_s1_lr_mem rev40_s1_ul_mem rev40_s1_ur_mem p
    (hp _ rev40_plane31_mem) (hp _ rev40_plane49_mem) hx0 hx1
def rev40_s2_ll : FractionPoint := ⟨11440249932738727,48928332174000000,2025309014539974239493,5251412654459188000000⟩
theorem rev40_s2_ll_mem : rev40_s2_ll.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane31 rev40_vertex4 rev40_vertex0 rev40_s2_ll
    rev40_vertex4_mem rev40_vertex0_mem (by decide)
def rev40_s2_lr : FractionPoint := ⟨611446104810513,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev40_s2_lr_mem : rev40_s2_lr.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane31 rev40_vertex4 rev40_vertex0 rev40_s2_lr
    rev40_vertex4_mem rev40_vertex0_mem (by decide)
def rev40_s2_ul : FractionPoint := ⟨11440249932738727,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev40_s2_ul_mem : rev40_s2_ul.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane13 rev40_vertex2 rev40_vertex1 rev40_s2_ul
    rev40_vertex2_mem rev40_vertex1_mem (by decide)
def rev40_s2_ur : FractionPoint := ⟨611446104810513,2546743666000000,150679115621052151573,311718877974734000000⟩
theorem rev40_s2_ur_mem : rev40_s2_ur.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane13 rev40_vertex2 rev40_vertex1 rev40_s2_ur
    rev40_vertex2_mem rev40_vertex1_mem (by decide)
theorem rev40_slab2 (p : Point) (hp : p∈IntegerCarrier rev40_planes)
    (hx0 : rev40_s2_ll.real.1≤p.1) (hx1 : p.1≤rev40_s2_lr.real.1) :
    p∈rationalHull (fractionRow40.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev40_plane31 rev40_plane13 rev40_s2_ll rev40_s2_lr rev40_s2_ul rev40_s2_ur
    (by decide) rev40_s2_ll_mem rev40_s2_lr_mem rev40_s2_ul_mem rev40_s2_ur_mem p
    (hp _ rev40_plane31_mem) (hp _ rev40_plane13_mem) hx0 hx1
def rev40_s3_ll : FractionPoint := ⟨611446104810513,2546743666000000,1862939987124017,5093487332000000⟩
theorem rev40_s3_ll_mem : rev40_s3_ll.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane9 rev40_vertex0 rev40_vertex1 rev40_s3_ll
    rev40_vertex0_mem rev40_vertex1_mem (by decide)
def rev40_s3_lr : FractionPoint := ⟨29287950748577,109987485000000,3270661284241,7332499000000⟩
theorem rev40_s3_lr_mem : rev40_s3_lr.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane9 rev40_vertex0 rev40_vertex1 rev40_s3_lr
    rev40_vertex0_mem rev40_vertex1_mem (by decide)
def rev40_s3_ul : FractionPoint := ⟨611446104810513,2546743666000000,150679115621052151573,311718877974734000000⟩
theorem rev40_s3_ul_mem : rev40_s3_ul.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane13 rev40_vertex2 rev40_vertex1 rev40_s3_ul
    rev40_vertex2_mem rev40_vertex1_mem (by decide)
def rev40_s3_ur : FractionPoint := ⟨29287950748577,109987485000000,3270661284241,7332499000000⟩
theorem rev40_s3_ur_mem : rev40_s3_ur.real ∈ rationalHull (fractionRow40.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow40 rev40_plane13 rev40_vertex2 rev40_vertex1 rev40_s3_ur
    rev40_vertex2_mem rev40_vertex1_mem (by decide)
theorem rev40_slab3 (p : Point) (hp : p∈IntegerCarrier rev40_planes)
    (hx0 : rev40_s3_ll.real.1≤p.1) (hx1 : p.1≤rev40_s3_lr.real.1) :
    p∈rationalHull (fractionRow40.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev40_plane9 rev40_plane13 rev40_s3_ll rev40_s3_lr rev40_s3_ul rev40_s3_ur
    (by decide) rev40_s3_ll_mem rev40_s3_lr_mem rev40_s3_ul_mem rev40_s3_ur_mem p
    (hp _ rev40_plane9_mem) (hp _ rev40_plane13_mem) hx0 hx1
theorem rev40_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev40_planes) : rev40_s0_ll.real.1≤p.1 := by
  have hc := rev40_plane31.combine_sound rev40_plane35 1468788000000 643972000000 (by decide) (by decide) p
    (hp _ rev40_plane31_mem) (hp _ rev40_plane35_mem)
  exact (rev40_plane31.combine rev40_plane35 1468788000000 643972000000).xBoundCheck_sound rev40_s0_ll.nx rev40_s0_ll.dx true (by decide) p hc
theorem rev40_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev40_planes) : p.1≤rev40_s3_lr.real.1 := by
  have hc := rev40_plane9.combine_sound rev40_plane13 1468788000000 699568000000 (by decide) (by decide) p
    (hp _ rev40_plane9_mem) (hp _ rev40_plane13_mem)
  exact (rev40_plane9.combine rev40_plane13 1468788000000 699568000000).xBoundCheck_sound rev40_s3_lr.nx rev40_s3_lr.dx false (by decide) p hc
theorem rev40_hull (p : Point) (hp : p∈IntegerCarrier rev40_planes) :
    p∈rationalHull (fractionRow40.map FractionPoint.rational) := by
  have hxlo := rev40_bound0_lo p hp
  have hxhi := rev40_bound0_hi p hp
  by_cases h0 : p.1≤rev40_s0_lr.real.1
  · exact rev40_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev40_s1_lr.real.1
  · exact rev40_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev40_s2_lr.real.1
  · exact rev40_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev40_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull40 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,6,2,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow40 := by
  rw [← fractionRow40_correct]
  exact rev40_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull40
