import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks7
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev61_planes : List IntegerPlane := integerOverlayPlanes ![5,2,11,4]
def rev61_plane5 : IntegerPlane := ⟨16372000000,(-2139440000000),(-377332847425)⟩
theorem rev61_plane5_mem : rev61_plane5 ∈ rev61_planes := by decide
def rev61_plane6 : IntegerPlane := ⟨2099728000000,(-1393416000000),740183860516⟩
theorem rev61_plane6_mem : rev61_plane6 ∈ rev61_planes := by decide
def rev61_plane29 : IntegerPlane := ⟨2099728000000,1393416000000,1359544139484⟩
theorem rev61_plane29_mem : rev61_plane29 ∈ rev61_planes := by decide
def rev61_plane50 : IntegerPlane := ⟨(-1468788000000),2093220000000,(-256243273104)⟩
theorem rev61_plane50_mem : rev61_plane50 ∈ rev61_planes := by decide
def rev61_plane51 : IntegerPlane := ⟨(-2112760000000),48252000000,(-982750749085)⟩
theorem rev61_plane51_mem : rev61_plane51 ∈ rev61_planes := by decide
def rev61_vertex0 : FractionPoint := fractionRow61[0]!
theorem rev61_vertex0_mem : rev61_vertex0∈fractionRow61 := by decide
def rev61_vertex1 : FractionPoint := fractionRow61[1]!
theorem rev61_vertex1_mem : rev61_vertex1∈fractionRow61 := by decide
def rev61_vertex2 : FractionPoint := fractionRow61[2]!
theorem rev61_vertex2_mem : rev61_vertex2∈fractionRow61 := by decide
def rev61_vertex3 : FractionPoint := fractionRow61[3]!
theorem rev61_vertex3_mem : rev61_vertex3∈fractionRow61 := by decide
def rev61_vertex4 : FractionPoint := fractionRow61[4]!
theorem rev61_vertex4_mem : rev61_vertex4∈fractionRow61 := by decide
def rev61_s0_ll : FractionPoint := ⟨4241486654352727,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev61_s0_ll_mem : rev61_s0_ll.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane5 rev61_vertex0 rev61_vertex1 rev61_s0_ll
    rev61_vertex0_mem rev61_vertex1_mem (by decide)
def rev61_s0_lr : FractionPoint := ⟨56798590905163597,120877764684000000,2908816104305135234299,16163170304721060000000⟩
theorem rev61_s0_lr_mem : rev61_s0_lr.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane5 rev61_vertex0 rev61_vertex1 rev61_s0_lr
    rev61_vertex0_mem rev61_vertex1_mem (by decide)
def rev61_s0_ul : FractionPoint := ⟨4241486654352727,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev61_s0_ul_mem : rev61_s0_ul.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane51 rev61_vertex0 rev61_vertex4 rev61_s0_ul
    rev61_vertex0_mem rev61_vertex4_mem (by decide)
def rev61_s0_ur : FractionPoint := ⟨56798590905163597,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev61_s0_ur_mem : rev61_s0_ur.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane51 rev61_vertex0 rev61_vertex4 rev61_s0_ur
    rev61_vertex0_mem rev61_vertex4_mem (by decide)
theorem rev61_slab0 (p : Point) (hp : p∈IntegerCarrier rev61_planes)
    (hx0 : rev61_s0_ll.real.1≤p.1) (hx1 : p.1≤rev61_s0_lr.real.1) :
    p∈rationalHull (fractionRow61.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev61_plane5 rev61_plane51 rev61_s0_ll rev61_s0_lr rev61_s0_ul rev61_s0_ur
    (by decide) rev61_s0_ll_mem rev61_s0_lr_mem rev61_s0_ul_mem rev61_s0_ur_mem p
    (hp _ rev61_plane5_mem) (hp _ rev61_plane51_mem) hx0 hx1
def rev61_s1_ll : FractionPoint := ⟨56798590905163597,120877764684000000,2908816104305135234299,16163170304721060000000⟩
theorem rev61_s1_ll_mem : rev61_s1_ll.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane5 rev61_vertex0 rev61_vertex1 rev61_s1_ll
    rev61_vertex0_mem rev61_vertex1_mem (by decide)
def rev61_s1_lr : FractionPoint := ⟨52734014636747621,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev61_s1_lr_mem : rev61_s1_lr.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane5 rev61_vertex0 rev61_vertex1 rev61_s1_lr
    rev61_vertex0_mem rev61_vertex1_mem (by decide)
def rev61_s1_ul : FractionPoint := ⟨56798590905163597,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev61_s1_ul_mem : rev61_s1_ul.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane50 rev61_vertex4 rev61_vertex3 rev61_s1_ul
    rev61_vertex4_mem rev61_vertex3_mem (by decide)
def rev61_s1_ur : FractionPoint := ⟨52734014636747621,111735726639200000,20343149822332021283863,97453107381544260000000⟩
theorem rev61_s1_ur_mem : rev61_s1_ur.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane50 rev61_vertex4 rev61_vertex3 rev61_s1_ur
    rev61_vertex4_mem rev61_vertex3_mem (by decide)
theorem rev61_slab1 (p : Point) (hp : p∈IntegerCarrier rev61_planes)
    (hx0 : rev61_s1_ll.real.1≤p.1) (hx1 : p.1≤rev61_s1_lr.real.1) :
    p∈rationalHull (fractionRow61.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev61_plane5 rev61_plane50 rev61_s1_ll rev61_s1_lr rev61_s1_ul rev61_s1_ur
    (by decide) rev61_s1_ll_mem rev61_s1_lr_mem rev61_s1_ul_mem rev61_s1_ur_mem p
    (hp _ rev61_plane5_mem) (hp _ rev61_plane50_mem) hx0 hx1
def rev61_s2_ll : FractionPoint := ⟨52734014636747621,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev61_s2_ll_mem : rev61_s2_ll.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane6 rev61_vertex1 rev61_vertex2 rev61_s2_ll
    rev61_vertex1_mem rev61_vertex2_mem (by decide)
def rev61_s2_lr : FractionPoint := ⟨22242211529765151,44734898222000000,1698818083152552072047,7791790367613294000000⟩
theorem rev61_s2_lr_mem : rev61_s2_lr.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane6 rev61_vertex1 rev61_vertex2 rev61_s2_lr
    rev61_vertex1_mem rev61_vertex2_mem (by decide)
def rev61_s2_ul : FractionPoint := ⟨52734014636747621,111735726639200000,20343149822332021283863,97453107381544260000000⟩
theorem rev61_s2_ul_mem : rev61_s2_ul.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane50 rev61_vertex4 rev61_vertex3 rev61_s2_ul
    rev61_vertex4_mem rev61_vertex3_mem (by decide)
def rev61_s2_ur : FractionPoint := ⟨22242211529765151,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev61_s2_ur_mem : rev61_s2_ur.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane50 rev61_vertex4 rev61_vertex3 rev61_s2_ur
    rev61_vertex4_mem rev61_vertex3_mem (by decide)
theorem rev61_slab2 (p : Point) (hp : p∈IntegerCarrier rev61_planes)
    (hx0 : rev61_s2_ll.real.1≤p.1) (hx1 : p.1≤rev61_s2_lr.real.1) :
    p∈rationalHull (fractionRow61.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev61_plane6 rev61_plane50 rev61_s2_ll rev61_s2_lr rev61_s2_ul rev61_s2_ur
    (by decide) rev61_s2_ll_mem rev61_s2_lr_mem rev61_s2_ul_mem rev61_s2_ur_mem p
    (hp _ rev61_plane6_mem) (hp _ rev61_plane50_mem) hx0 hx1
def rev61_s3_ll : FractionPoint := ⟨22242211529765151,44734898222000000,1698818083152552072047,7791790367613294000000⟩
theorem rev61_s3_ll_mem : rev61_s3_ll.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane6 rev61_vertex1 rev61_vertex2 rev61_s3_ll
    rev61_vertex1_mem rev61_vertex2_mem (by decide)
def rev61_s3_lr : FractionPoint := ⟨1,2,77420034871,348354000000⟩
theorem rev61_s3_lr_mem : rev61_s3_lr.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane6 rev61_vertex1 rev61_vertex2 rev61_s3_lr
    rev61_vertex1_mem rev61_vertex2_mem (by decide)
def rev61_s3_ul : FractionPoint := ⟨22242211529765151,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev61_s3_ul_mem : rev61_s3_ul.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane29 rev61_vertex3 rev61_vertex2 rev61_s3_ul
    rev61_vertex3_mem rev61_vertex2_mem (by decide)
def rev61_s3_ur : FractionPoint := ⟨1,2,77420034871,348354000000⟩
theorem rev61_s3_ur_mem : rev61_s3_ur.real ∈ rationalHull (fractionRow61.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow61 rev61_plane29 rev61_vertex3 rev61_vertex2 rev61_s3_ur
    rev61_vertex3_mem rev61_vertex2_mem (by decide)
theorem rev61_slab3 (p : Point) (hp : p∈IntegerCarrier rev61_planes)
    (hx0 : rev61_s3_ll.real.1≤p.1) (hx1 : p.1≤rev61_s3_lr.real.1) :
    p∈rationalHull (fractionRow61.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev61_plane6 rev61_plane29 rev61_s3_ll rev61_s3_lr rev61_s3_ul rev61_s3_ur
    (by decide) rev61_s3_ll_mem rev61_s3_lr_mem rev61_s3_ul_mem rev61_s3_ur_mem p
    (hp _ rev61_plane6_mem) (hp _ rev61_plane29_mem) hx0 hx1
theorem rev61_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev61_planes) : rev61_s0_ll.real.1≤p.1 := by
  have hc := rev61_plane5.combine_sound rev61_plane51 48252000000 2139440000000 (by decide) (by decide) p
    (hp _ rev61_plane5_mem) (hp _ rev61_plane51_mem)
  exact (rev61_plane5.combine rev61_plane51 48252000000 2139440000000).xBoundCheck_sound rev61_s0_ll.nx rev61_s0_ll.dx true (by decide) p hc
theorem rev61_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev61_planes) : p.1≤rev61_s3_lr.real.1 := by
  have hc := rev61_plane6.combine_sound rev61_plane29 1393416000000 1393416000000 (by decide) (by decide) p
    (hp _ rev61_plane6_mem) (hp _ rev61_plane29_mem)
  exact (rev61_plane6.combine rev61_plane29 1393416000000 1393416000000).xBoundCheck_sound rev61_s3_lr.nx rev61_s3_lr.dx false (by decide) p hc
theorem rev61_hull (p : Point) (hp : p∈IntegerCarrier rev61_planes) :
    p∈rationalHull (fractionRow61.map FractionPoint.rational) := by
  have hxlo := rev61_bound0_lo p hp
  have hxhi := rev61_bound0_hi p hp
  by_cases h0 : p.1≤rev61_s0_lr.real.1
  · exact rev61_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev61_s1_lr.real.1
  · exact rev61_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev61_s2_lr.real.1
  · exact rev61_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev61_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull61 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,2,11,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow61 := by
  rw [← fractionRow61_correct]
  exact rev61_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull61
