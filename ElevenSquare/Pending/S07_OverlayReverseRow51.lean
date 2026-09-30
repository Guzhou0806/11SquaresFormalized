import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks6
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev51_planes : List IntegerPlane := integerOverlayPlanes ![4,11,2,5]
def rev51_plane30 : IntegerPlane := ⟨2093220000000,(-1468788000000),(-256243273104)⟩
theorem rev51_plane30_mem : rev51_plane30 ∈ rev51_planes := by decide
def rev51_plane31 : IntegerPlane := ⟨48252000000,(-2112760000000),(-982750749085)⟩
theorem rev51_plane31_mem : rev51_plane31 ∈ rev51_planes := by decide
def rev51_plane49 : IntegerPlane := ⟨1393416000000,2099728000000,1359544139484⟩
theorem rev51_plane49_mem : rev51_plane49 ∈ rev51_planes := by decide
def rev51_plane65 : IntegerPlane := ⟨(-2139440000000),16372000000,(-377332847425)⟩
theorem rev51_plane65_mem : rev51_plane65 ∈ rev51_planes := by decide
def rev51_plane66 : IntegerPlane := ⟨(-1393416000000),2099728000000,740183860516⟩
theorem rev51_plane66_mem : rev51_plane66 ∈ rev51_planes := by decide
def rev51_vertex0 : FractionPoint := fractionRow51[0]!
theorem rev51_vertex0_mem : rev51_vertex0∈fractionRow51 := by decide
def rev51_vertex1 : FractionPoint := fractionRow51[1]!
theorem rev51_vertex1_mem : rev51_vertex1∈fractionRow51 := by decide
def rev51_vertex2 : FractionPoint := fractionRow51[2]!
theorem rev51_vertex2_mem : rev51_vertex2∈fractionRow51 := by decide
def rev51_vertex3 : FractionPoint := fractionRow51[3]!
theorem rev51_vertex3_mem : rev51_vertex3∈fractionRow51 := by decide
def rev51_vertex4 : FractionPoint := fractionRow51[4]!
theorem rev51_vertex4_mem : rev51_vertex4∈fractionRow51 := by decide
def rev51_s0_ll : FractionPoint := ⟨40665167099483131,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev51_s0_ll_mem : rev51_s0_ll.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane31 rev51_vertex0 rev51_vertex1 rev51_s0_ll
    rev51_vertex0_mem rev51_vertex1_mem (by decide)
def rev51_s0_lr : FractionPoint := ⟨25137957350699011,139669658299000000,138473418035874165585187,295088467267795240000000⟩
theorem rev51_s0_lr_mem : rev51_s0_lr.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane31 rev51_vertex0 rev51_vertex1 rev51_s0_lr
    rev51_vertex0_mem rev51_vertex1_mem (by decide)
def rev51_s0_ul : FractionPoint := ⟨40665167099483131,225966663632800000,4241486654352727,9038666545312000⟩
theorem rev51_s0_ul_mem : rev51_s0_ul.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane65 rev51_vertex0 rev51_vertex4 rev51_s0_ul
    rev51_vertex0_mem rev51_vertex4_mem (by decide)
def rev51_s0_ur : FractionPoint := ⟨25137957350699011,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev51_s0_ur_mem : rev51_s0_ur.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane65 rev51_vertex0 rev51_vertex4 rev51_s0_ur
    rev51_vertex0_mem rev51_vertex4_mem (by decide)
theorem rev51_slab0 (p : Point) (hp : p∈IntegerCarrier rev51_planes)
    (hx0 : rev51_s0_ll.real.1≤p.1) (hx1 : p.1≤rev51_s0_lr.real.1) :
    p∈rationalHull (fractionRow51.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev51_plane31 rev51_plane65 rev51_s0_ll rev51_s0_lr rev51_s0_ul rev51_s0_ur
    (by decide) rev51_s0_ll_mem rev51_s0_lr_mem rev51_s0_ul_mem rev51_s0_ur_mem p
    (hp _ rev51_plane31_mem) (hp _ rev51_plane65_mem) hx0 hx1
def rev51_s1_ll : FractionPoint := ⟨25137957350699011,139669658299000000,138473418035874165585187,295088467267795240000000⟩
theorem rev51_s1_ll_mem : rev51_s1_ll.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane31 rev51_vertex0 rev51_vertex1 rev51_s1_ll
    rev51_vertex0_mem rev51_vertex1_mem (by decide)
def rev51_s1_lr : FractionPoint := ⟨15034532826064199,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev51_s1_lr_mem : rev51_s1_lr.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane31 rev51_vertex0 rev51_vertex1 rev51_s1_lr
    rev51_vertex0_mem rev51_vertex1_mem (by decide)
def rev51_s1_ul : FractionPoint := ⟨25137957350699011,139669658299000000,52734014636747621,111735726639200000⟩
theorem rev51_s1_ul_mem : rev51_s1_ul.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane66 rev51_vertex4 rev51_vertex3 rev51_s1_ul
    rev51_vertex4_mem rev51_vertex3_mem (by decide)
def rev51_s1_ur : FractionPoint := ⟨15034532826064199,72526658810400000,5182807007011924166941,10575434461850248000000⟩
theorem rev51_s1_ur_mem : rev51_s1_ur.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane66 rev51_vertex4 rev51_vertex3 rev51_s1_ur
    rev51_vertex4_mem rev51_vertex3_mem (by decide)
theorem rev51_slab1 (p : Point) (hp : p∈IntegerCarrier rev51_planes)
    (hx0 : rev51_s1_ll.real.1≤p.1) (hx1 : p.1≤rev51_s1_lr.real.1) :
    p∈rationalHull (fractionRow51.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev51_plane31 rev51_plane66 rev51_s1_ll rev51_s1_lr rev51_s1_ul rev51_s1_ur
    (by decide) rev51_s1_ll_mem rev51_s1_lr_mem rev51_s1_ul_mem rev51_s1_ur_mem p
    (hp _ rev51_plane31_mem) (hp _ rev51_plane66_mem) hx0 hx1
def rev51_s2_ll : FractionPoint := ⟨15034532826064199,72526658810400000,56798590905163597,120877764684000000⟩
theorem rev51_s2_ll_mem : rev51_s2_ll.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane30 rev51_vertex1 rev51_vertex2 rev51_s2_ll
    rev51_vertex1_mem rev51_vertex2_mem (by decide)
def rev51_s2_lr : FractionPoint := ⟨77420034871,348354000000,6981125959765151,14212727082000000⟩
theorem rev51_s2_lr_mem : rev51_s2_lr.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane30 rev51_vertex1 rev51_vertex2 rev51_s2_lr
    rev51_vertex1_mem rev51_vertex2_mem (by decide)
def rev51_s2_ul : FractionPoint := ⟨15034532826064199,72526658810400000,5182807007011924166941,10575434461850248000000⟩
theorem rev51_s2_ul_mem : rev51_s2_ul.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane66 rev51_vertex4 rev51_vertex3 rev51_s2_ul
    rev51_vertex4_mem rev51_vertex3_mem (by decide)
def rev51_s2_ur : FractionPoint := ⟨77420034871,348354000000,1,2⟩
theorem rev51_s2_ur_mem : rev51_s2_ur.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane66 rev51_vertex4 rev51_vertex3 rev51_s2_ur
    rev51_vertex4_mem rev51_vertex3_mem (by decide)
theorem rev51_slab2 (p : Point) (hp : p∈IntegerCarrier rev51_planes)
    (hx0 : rev51_s2_ll.real.1≤p.1) (hx1 : p.1≤rev51_s2_lr.real.1) :
    p∈rationalHull (fractionRow51.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev51_plane30 rev51_plane66 rev51_s2_ll rev51_s2_lr rev51_s2_ul rev51_s2_ur
    (by decide) rev51_s2_ll_mem rev51_s2_lr_mem rev51_s2_ul_mem rev51_s2_ur_mem p
    (hp _ rev51_plane30_mem) (hp _ rev51_plane66_mem) hx0 hx1
def rev51_s3_ll : FractionPoint := ⟨77420034871,348354000000,6981125959765151,14212727082000000⟩
theorem rev51_s3_ll_mem : rev51_s3_ll.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane30 rev51_vertex1 rev51_vertex2 rev51_s3_ll
    rev51_vertex1_mem rev51_vertex2_mem (by decide)
def rev51_s3_lr : FractionPoint := ⟨6078503925817957,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev51_s3_lr_mem : rev51_s3_lr.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane30 rev51_vertex1 rev51_vertex2 rev51_s3_lr
    rev51_vertex1_mem rev51_vertex2_mem (by decide)
def rev51_s3_ul : FractionPoint := ⟨77420034871,348354000000,1,2⟩
theorem rev51_s3_ul_mem : rev51_s3_ul.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane49 rev51_vertex3 rev51_vertex2 rev51_s3_ul
    rev51_vertex3_mem rev51_vertex2_mem (by decide)
def rev51_s3_ur : FractionPoint := ⟨6078503925817957,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev51_s3_ur_mem : rev51_s3_ur.real ∈ rationalHull (fractionRow51.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow51 rev51_plane49 rev51_vertex3 rev51_vertex2 rev51_s3_ur
    rev51_vertex3_mem rev51_vertex2_mem (by decide)
theorem rev51_slab3 (p : Point) (hp : p∈IntegerCarrier rev51_planes)
    (hx0 : rev51_s3_ll.real.1≤p.1) (hx1 : p.1≤rev51_s3_lr.real.1) :
    p∈rationalHull (fractionRow51.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev51_plane30 rev51_plane49 rev51_s3_ll rev51_s3_lr rev51_s3_ul rev51_s3_ur
    (by decide) rev51_s3_ll_mem rev51_s3_lr_mem rev51_s3_ul_mem rev51_s3_ur_mem p
    (hp _ rev51_plane30_mem) (hp _ rev51_plane49_mem) hx0 hx1
theorem rev51_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev51_planes) : rev51_s0_ll.real.1≤p.1 := by
  have hc := rev51_plane31.combine_sound rev51_plane65 16372000000 2112760000000 (by decide) (by decide) p
    (hp _ rev51_plane31_mem) (hp _ rev51_plane65_mem)
  exact (rev51_plane31.combine rev51_plane65 16372000000 2112760000000).xBoundCheck_sound rev51_s0_ll.nx rev51_s0_ll.dx true (by decide) p hc
theorem rev51_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev51_planes) : p.1≤rev51_s3_lr.real.1 := by
  have hc := rev51_plane30.combine_sound rev51_plane49 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev51_plane30_mem) (hp _ rev51_plane49_mem)
  exact (rev51_plane30.combine rev51_plane49 2099728000000 1468788000000).xBoundCheck_sound rev51_s3_lr.nx rev51_s3_lr.dx false (by decide) p hc
theorem rev51_hull (p : Point) (hp : p∈IntegerCarrier rev51_planes) :
    p∈rationalHull (fractionRow51.map FractionPoint.rational) := by
  have hxlo := rev51_bound0_lo p hp
  have hxhi := rev51_bound0_hi p hp
  by_cases h0 : p.1≤rev51_s0_lr.real.1
  · exact rev51_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev51_s1_lr.real.1
  · exact rev51_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev51_s2_lr.real.1
  · exact rev51_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev51_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull51 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,11,2,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow51 := by
  rw [← fractionRow51_correct]
  exact rev51_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull51
