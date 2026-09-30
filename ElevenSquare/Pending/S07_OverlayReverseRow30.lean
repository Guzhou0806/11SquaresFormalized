import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks3
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev30_planes : List IntegerPlane := integerOverlayPlanes ![2,5,11,4]
def rev30_plane9 : IntegerPlane := ⟨(-2099728000000),1393416000000,(-740183860516)⟩
theorem rev30_plane9_mem : rev30_plane9 ∈ rev30_planes := by decide
def rev30_plane25 : IntegerPlane := ⟨(-16372000000),(-2139440000000),(-393704847425)⟩
theorem rev30_plane25_mem : rev30_plane25 ∈ rev30_planes := by decide
def rev30_plane26 : IntegerPlane := ⟨(-2099728000000),(-1393416000000),(-1359544139484)⟩
theorem rev30_plane26_mem : rev30_plane26 ∈ rev30_planes := by decide
def rev30_plane72 : IntegerPlane := ⟨2112760000000,48252000000,1130009250915⟩
theorem rev30_plane72_mem : rev30_plane72 ∈ rev30_planes := by decide
def rev30_plane73 : IntegerPlane := ⟨1468788000000,2093220000000,1212544726896⟩
theorem rev30_plane73_mem : rev30_plane73 ∈ rev30_planes := by decide
def rev30_vertex0 : FractionPoint := fractionRow30[0]!
theorem rev30_vertex0_mem : rev30_vertex0∈fractionRow30 := by decide
def rev30_vertex1 : FractionPoint := fractionRow30[1]!
theorem rev30_vertex1_mem : rev30_vertex1∈fractionRow30 := by decide
def rev30_vertex2 : FractionPoint := fractionRow30[2]!
theorem rev30_vertex2_mem : rev30_vertex2∈fractionRow30 := by decide
def rev30_vertex3 : FractionPoint := fractionRow30[3]!
theorem rev30_vertex3_mem : rev30_vertex3∈fractionRow30 := by decide
def rev30_vertex4 : FractionPoint := fractionRow30[4]!
theorem rev30_vertex4_mem : rev30_vertex4∈fractionRow30 := by decide
def rev30_s0_ll : FractionPoint := ⟨1,2,77420034871,348354000000⟩
theorem rev30_s0_ll_mem : rev30_s0_ll.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane26 rev30_vertex1 rev30_vertex2 rev30_s0_ll
    rev30_vertex1_mem rev30_vertex2_mem (by decide)
def rev30_s0_lr : FractionPoint := ⟨22492686692234849,44734898222000000,1698818083152552072047,7791790367613294000000⟩
theorem rev30_s0_lr_mem : rev30_s0_lr.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane26 rev30_vertex1 rev30_vertex2 rev30_s0_lr
    rev30_vertex1_mem rev30_vertex2_mem (by decide)
def rev30_s0_ul : FractionPoint := ⟨1,2,77420034871,348354000000⟩
theorem rev30_s0_ul_mem : rev30_s0_ul.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane9 rev30_vertex1 rev30_vertex0 rev30_s0_ul
    rev30_vertex1_mem rev30_vertex0_mem (by decide)
def rev30_s0_ur : FractionPoint := ⟨22492686692234849,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev30_s0_ur_mem : rev30_s0_ur.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane9 rev30_vertex1 rev30_vertex0 rev30_s0_ur
    rev30_vertex1_mem rev30_vertex0_mem (by decide)
theorem rev30_slab0 (p : Point) (hp : p∈IntegerCarrier rev30_planes)
    (hx0 : rev30_s0_ll.real.1≤p.1) (hx1 : p.1≤rev30_s0_lr.real.1) :
    p∈rationalHull (fractionRow30.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev30_plane26 rev30_plane9 rev30_s0_ll rev30_s0_lr rev30_s0_ul rev30_s0_ur
    (by decide) rev30_s0_ll_mem rev30_s0_lr_mem rev30_s0_ul_mem rev30_s0_ur_mem p
    (hp _ rev30_plane26_mem) (hp _ rev30_plane9_mem) hx0 hx1
def rev30_s1_ll : FractionPoint := ⟨22492686692234849,44734898222000000,1698818083152552072047,7791790367613294000000⟩
theorem rev30_s1_ll_mem : rev30_s1_ll.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane26 rev30_vertex1 rev30_vertex2 rev30_s1_ll
    rev30_vertex1_mem rev30_vertex2_mem (by decide)
def rev30_s1_lr : FractionPoint := ⟨59001712002452379,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev30_s1_lr_mem : rev30_s1_lr.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane26 rev30_vertex1 rev30_vertex2 rev30_s1_lr
    rev30_vertex1_mem rev30_vertex2_mem (by decide)
def rev30_s1_ul : FractionPoint := ⟨22492686692234849,44734898222000000,6078503925817957,26840938933200000⟩
theorem rev30_s1_ul_mem : rev30_s1_ul.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane73 rev30_vertex0 rev30_vertex4 rev30_s1_ul
    rev30_vertex0_mem rev30_vertex4_mem (by decide)
def rev30_s1_ur : FractionPoint := ⟨59001712002452379,111735726639200000,20343149822332021283863,97453107381544260000000⟩
theorem rev30_s1_ur_mem : rev30_s1_ur.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane73 rev30_vertex0 rev30_vertex4 rev30_s1_ur
    rev30_vertex0_mem rev30_vertex4_mem (by decide)
theorem rev30_slab1 (p : Point) (hp : p∈IntegerCarrier rev30_planes)
    (hx0 : rev30_s1_ll.real.1≤p.1) (hx1 : p.1≤rev30_s1_lr.real.1) :
    p∈rationalHull (fractionRow30.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev30_plane26 rev30_plane73 rev30_s1_ll rev30_s1_lr rev30_s1_ul rev30_s1_ur
    (by decide) rev30_s1_ll_mem rev30_s1_lr_mem rev30_s1_ul_mem rev30_s1_ur_mem p
    (hp _ rev30_plane26_mem) (hp _ rev30_plane73_mem) hx0 hx1
def rev30_s2_ll : FractionPoint := ⟨59001712002452379,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev30_s2_ll_mem : rev30_s2_ll.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane25 rev30_vertex2 rev30_vertex3 rev30_s2_ll
    rev30_vertex2_mem rev30_vertex3_mem (by decide)
def rev30_s2_lr : FractionPoint := ⟨64079173778836403,120877764684000000,2908816104305135234299,16163170304721060000000⟩
theorem rev30_s2_lr_mem : rev30_s2_lr.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane25 rev30_vertex2 rev30_vertex3 rev30_s2_lr
    rev30_vertex2_mem rev30_vertex3_mem (by decide)
def rev30_s2_ul : FractionPoint := ⟨59001712002452379,111735726639200000,20343149822332021283863,97453107381544260000000⟩
theorem rev30_s2_ul_mem : rev30_s2_ul.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane73 rev30_vertex0 rev30_vertex4 rev30_s2_ul
    rev30_vertex0_mem rev30_vertex4_mem (by decide)
def rev30_s2_ur : FractionPoint := ⟨64079173778836403,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev30_s2_ur_mem : rev30_s2_ur.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane73 rev30_vertex0 rev30_vertex4 rev30_s2_ur
    rev30_vertex0_mem rev30_vertex4_mem (by decide)
theorem rev30_slab2 (p : Point) (hp : p∈IntegerCarrier rev30_planes)
    (hx0 : rev30_s2_ll.real.1≤p.1) (hx1 : p.1≤rev30_s2_lr.real.1) :
    p∈rationalHull (fractionRow30.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev30_plane25 rev30_plane73 rev30_s2_ll rev30_s2_lr rev30_s2_ul rev30_s2_ur
    (by decide) rev30_s2_ll_mem rev30_s2_lr_mem rev30_s2_ul_mem rev30_s2_ur_mem p
    (hp _ rev30_plane25_mem) (hp _ rev30_plane73_mem) hx0 hx1
def rev30_s3_ll : FractionPoint := ⟨64079173778836403,120877764684000000,2908816104305135234299,16163170304721060000000⟩
theorem rev30_s3_ll_mem : rev30_s3_ll.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane25 rev30_vertex2 rev30_vertex3 rev30_s3_ll
    rev30_vertex2_mem rev30_vertex3_mem (by decide)
def rev30_s3_lr : FractionPoint := ⟨4797179890959273,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev30_s3_lr_mem : rev30_s3_lr.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane25 rev30_vertex2 rev30_vertex3 rev30_s3_lr
    rev30_vertex2_mem rev30_vertex3_mem (by decide)
def rev30_s3_ul : FractionPoint := ⟨64079173778836403,120877764684000000,15034532826064199,72526658810400000⟩
theorem rev30_s3_ul_mem : rev30_s3_ul.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane72 rev30_vertex4 rev30_vertex3 rev30_s3_ul
    rev30_vertex4_mem rev30_vertex3_mem (by decide)
def rev30_s3_ur : FractionPoint := ⟨4797179890959273,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev30_s3_ur_mem : rev30_s3_ur.real ∈ rationalHull (fractionRow30.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow30 rev30_plane72 rev30_vertex4 rev30_vertex3 rev30_s3_ur
    rev30_vertex4_mem rev30_vertex3_mem (by decide)
theorem rev30_slab3 (p : Point) (hp : p∈IntegerCarrier rev30_planes)
    (hx0 : rev30_s3_ll.real.1≤p.1) (hx1 : p.1≤rev30_s3_lr.real.1) :
    p∈rationalHull (fractionRow30.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev30_plane25 rev30_plane72 rev30_s3_ll rev30_s3_lr rev30_s3_ul rev30_s3_ur
    (by decide) rev30_s3_ll_mem rev30_s3_lr_mem rev30_s3_ul_mem rev30_s3_ur_mem p
    (hp _ rev30_plane25_mem) (hp _ rev30_plane72_mem) hx0 hx1
theorem rev30_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev30_planes) : rev30_s0_ll.real.1≤p.1 := by
  have hc := rev30_plane9.combine_sound rev30_plane26 1393416000000 1393416000000 (by decide) (by decide) p
    (hp _ rev30_plane9_mem) (hp _ rev30_plane26_mem)
  exact (rev30_plane9.combine rev30_plane26 1393416000000 1393416000000).xBoundCheck_sound rev30_s0_ll.nx rev30_s0_ll.dx true (by decide) p hc
theorem rev30_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev30_planes) : p.1≤rev30_s3_lr.real.1 := by
  have hc := rev30_plane25.combine_sound rev30_plane72 48252000000 2139440000000 (by decide) (by decide) p
    (hp _ rev30_plane25_mem) (hp _ rev30_plane72_mem)
  exact (rev30_plane25.combine rev30_plane72 48252000000 2139440000000).xBoundCheck_sound rev30_s3_lr.nx rev30_s3_lr.dx false (by decide) p hc
theorem rev30_hull (p : Point) (hp : p∈IntegerCarrier rev30_planes) :
    p∈rationalHull (fractionRow30.map FractionPoint.rational) := by
  have hxlo := rev30_bound0_lo p hp
  have hxhi := rev30_bound0_hi p hp
  by_cases h0 : p.1≤rev30_s0_lr.real.1
  · exact rev30_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev30_s1_lr.real.1
  · exact rev30_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev30_s2_lr.real.1
  · exact rev30_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev30_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull30 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,5,11,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow30 := by
  rw [← fractionRow30_correct]
  exact rev30_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull30
