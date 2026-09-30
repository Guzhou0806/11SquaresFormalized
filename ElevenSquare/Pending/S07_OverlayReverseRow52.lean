import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks6
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev52_planes : List IntegerPlane := integerOverlayPlanes ![4,11,5,2]
def rev52_plane12 : IntegerPlane := ⟨48252000000,2112760000000,1130009250915⟩
theorem rev52_plane12_mem : rev52_plane12 ∈ rev52_planes := by decide
def rev52_plane13 : IntegerPlane := ⟨2093220000000,1468788000000,1212544726896⟩
theorem rev52_plane13_mem : rev52_plane13 ∈ rev52_planes := by decide
def rev52_plane45 : IntegerPlane := ⟨(-2139440000000),(-16372000000),(-393704847425)⟩
theorem rev52_plane45_mem : rev52_plane45 ∈ rev52_planes := by decide
def rev52_plane46 : IntegerPlane := ⟨(-1393416000000),(-2099728000000),(-1359544139484)⟩
theorem rev52_plane46_mem : rev52_plane46 ∈ rev52_planes := by decide
def rev52_plane69 : IntegerPlane := ⟨1393416000000,(-2099728000000),(-740183860516)⟩
theorem rev52_plane69_mem : rev52_plane69 ∈ rev52_planes := by decide
def rev52_vertex0 : FractionPoint := fractionRow52[0]!
theorem rev52_vertex0_mem : rev52_vertex0∈fractionRow52 := by decide
def rev52_vertex1 : FractionPoint := fractionRow52[1]!
theorem rev52_vertex1_mem : rev52_vertex1∈fractionRow52 := by decide
def rev52_vertex2 : FractionPoint := fractionRow52[2]!
theorem rev52_vertex2_mem : rev52_vertex2∈fractionRow52 := by decide
def rev52_vertex3 : FractionPoint := fractionRow52[3]!
theorem rev52_vertex3_mem : rev52_vertex3∈fractionRow52 := by decide
def rev52_vertex4 : FractionPoint := fractionRow52[4]!
theorem rev52_vertex4_mem : rev52_vertex4∈fractionRow52 := by decide
def rev52_s0_ll : FractionPoint := ⟨40665167099483131,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev52_s0_ll_mem : rev52_s0_ll.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane45 rev52_vertex2 rev52_vertex3 rev52_s0_ll
    rev52_vertex2_mem rev52_vertex3_mem (by decide)
def rev52_s0_lr : FractionPoint := ⟨25137957350699011,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev52_s0_lr_mem : rev52_s0_lr.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane45 rev52_vertex2 rev52_vertex3 rev52_s0_lr
    rev52_vertex2_mem rev52_vertex3_mem (by decide)
def rev52_s0_ul : FractionPoint := ⟨40665167099483131,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev52_s0_ul_mem : rev52_s0_ul.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane12 rev52_vertex2 rev52_vertex1 rev52_s0_ul
    rev52_vertex2_mem rev52_vertex1_mem (by decide)
def rev52_s0_ur : FractionPoint := ⟨25137957350699011,139669658299000000,156615049231921074414813,295088467267795240000000⟩
theorem rev52_s0_ur_mem : rev52_s0_ur.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane12 rev52_vertex2 rev52_vertex1 rev52_s0_ur
    rev52_vertex2_mem rev52_vertex1_mem (by decide)
theorem rev52_slab0 (p : Point) (hp : p∈IntegerCarrier rev52_planes)
    (hx0 : rev52_s0_ll.real.1≤p.1) (hx1 : p.1≤rev52_s0_lr.real.1) :
    p∈rationalHull (fractionRow52.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev52_plane45 rev52_plane12 rev52_s0_ll rev52_s0_lr rev52_s0_ul rev52_s0_ur
    (by decide) rev52_s0_ll_mem rev52_s0_lr_mem rev52_s0_ul_mem rev52_s0_ur_mem p
    (hp _ rev52_plane45_mem) (hp _ rev52_plane12_mem) hx0 hx1
def rev52_s1_ll : FractionPoint := ⟨25137957350699011,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev52_s1_ll_mem : rev52_s1_ll.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane46 rev52_vertex3 rev52_vertex4 rev52_s1_ll
    rev52_vertex3_mem rev52_vertex4_mem (by decide)
def rev52_s1_lr : FractionPoint := ⟨15034532826064199,72526658810400000,5392627454838323833059,10575434461850248000000⟩
theorem rev52_s1_lr_mem : rev52_s1_lr.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane46 rev52_vertex3 rev52_vertex4 rev52_s1_lr
    rev52_vertex3_mem rev52_vertex4_mem (by decide)
def rev52_s1_ul : FractionPoint := ⟨25137957350699011,139669658299000000,156615049231921074414813,295088467267795240000000⟩
theorem rev52_s1_ul_mem : rev52_s1_ul.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane12 rev52_vertex2 rev52_vertex1 rev52_s1_ul
    rev52_vertex2_mem rev52_vertex1_mem (by decide)
def rev52_s1_ur : FractionPoint := ⟨15034532826064199,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev52_s1_ur_mem : rev52_s1_ur.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane12 rev52_vertex2 rev52_vertex1 rev52_s1_ur
    rev52_vertex2_mem rev52_vertex1_mem (by decide)
theorem rev52_slab1 (p : Point) (hp : p∈IntegerCarrier rev52_planes)
    (hx0 : rev52_s1_ll.real.1≤p.1) (hx1 : p.1≤rev52_s1_lr.real.1) :
    p∈rationalHull (fractionRow52.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev52_plane46 rev52_plane12 rev52_s1_ll rev52_s1_lr rev52_s1_ul rev52_s1_ur
    (by decide) rev52_s1_ll_mem rev52_s1_lr_mem rev52_s1_ul_mem rev52_s1_ur_mem p
    (hp _ rev52_plane46_mem) (hp _ rev52_plane12_mem) hx0 hx1
def rev52_s2_ll : FractionPoint := ⟨15034532826064199,72526658810400000,5392627454838323833059,10575434461850248000000⟩
theorem rev52_s2_ll_mem : rev52_s2_ll.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane46 rev52_vertex3 rev52_vertex4 rev52_s2_ll
    rev52_vertex3_mem rev52_vertex4_mem (by decide)
def rev52_s2_lr : FractionPoint := ⟨77420034871,348354000000,1,2⟩
theorem rev52_s2_lr_mem : rev52_s2_lr.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane46 rev52_vertex3 rev52_vertex4 rev52_s2_lr
    rev52_vertex3_mem rev52_vertex4_mem (by decide)
def rev52_s2_ul : FractionPoint := ⟨15034532826064199,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev52_s2_ul_mem : rev52_s2_ul.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane13 rev52_vertex1 rev52_vertex0 rev52_s2_ul
    rev52_vertex1_mem rev52_vertex0_mem (by decide)
def rev52_s2_ur : FractionPoint := ⟨77420034871,348354000000,7231601122234849,14212727082000000⟩
theorem rev52_s2_ur_mem : rev52_s2_ur.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane13 rev52_vertex1 rev52_vertex0 rev52_s2_ur
    rev52_vertex1_mem rev52_vertex0_mem (by decide)
theorem rev52_slab2 (p : Point) (hp : p∈IntegerCarrier rev52_planes)
    (hx0 : rev52_s2_ll.real.1≤p.1) (hx1 : p.1≤rev52_s2_lr.real.1) :
    p∈rationalHull (fractionRow52.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev52_plane46 rev52_plane13 rev52_s2_ll rev52_s2_lr rev52_s2_ul rev52_s2_ur
    (by decide) rev52_s2_ll_mem rev52_s2_lr_mem rev52_s2_ul_mem rev52_s2_ur_mem p
    (hp _ rev52_plane46_mem) (hp _ rev52_plane13_mem) hx0 hx1
def rev52_s3_ll : FractionPoint := ⟨77420034871,348354000000,1,2⟩
theorem rev52_s3_ll_mem : rev52_s3_ll.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane69 rev52_vertex4 rev52_vertex0 rev52_s3_ll
    rev52_vertex4_mem rev52_vertex0_mem (by decide)
def rev52_s3_lr : FractionPoint := ⟨6078503925817957,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev52_s3_lr_mem : rev52_s3_lr.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane69 rev52_vertex4 rev52_vertex0 rev52_s3_lr
    rev52_vertex4_mem rev52_vertex0_mem (by decide)
def rev52_s3_ul : FractionPoint := ⟨77420034871,348354000000,7231601122234849,14212727082000000⟩
theorem rev52_s3_ul_mem : rev52_s3_ul.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane13 rev52_vertex1 rev52_vertex0 rev52_s3_ul
    rev52_vertex1_mem rev52_vertex0_mem (by decide)
def rev52_s3_ur : FractionPoint := ⟨6078503925817957,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev52_s3_ur_mem : rev52_s3_ur.real ∈ rationalHull (fractionRow52.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow52 rev52_plane13 rev52_vertex1 rev52_vertex0 rev52_s3_ur
    rev52_vertex1_mem rev52_vertex0_mem (by decide)
theorem rev52_slab3 (p : Point) (hp : p∈IntegerCarrier rev52_planes)
    (hx0 : rev52_s3_ll.real.1≤p.1) (hx1 : p.1≤rev52_s3_lr.real.1) :
    p∈rationalHull (fractionRow52.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev52_plane69 rev52_plane13 rev52_s3_ll rev52_s3_lr rev52_s3_ul rev52_s3_ur
    (by decide) rev52_s3_ll_mem rev52_s3_lr_mem rev52_s3_ul_mem rev52_s3_ur_mem p
    (hp _ rev52_plane69_mem) (hp _ rev52_plane13_mem) hx0 hx1
theorem rev52_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev52_planes) : rev52_s0_ll.real.1≤p.1 := by
  have hc := rev52_plane12.combine_sound rev52_plane45 16372000000 2112760000000 (by decide) (by decide) p
    (hp _ rev52_plane12_mem) (hp _ rev52_plane45_mem)
  exact (rev52_plane12.combine rev52_plane45 16372000000 2112760000000).xBoundCheck_sound rev52_s0_ll.nx rev52_s0_ll.dx true (by decide) p hc
theorem rev52_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev52_planes) : p.1≤rev52_s3_lr.real.1 := by
  have hc := rev52_plane13.combine_sound rev52_plane69 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev52_plane13_mem) (hp _ rev52_plane69_mem)
  exact (rev52_plane13.combine rev52_plane69 2099728000000 1468788000000).xBoundCheck_sound rev52_s3_lr.nx rev52_s3_lr.dx false (by decide) p hc
theorem rev52_hull (p : Point) (hp : p∈IntegerCarrier rev52_planes) :
    p∈rationalHull (fractionRow52.map FractionPoint.rational) := by
  have hxlo := rev52_bound0_lo p hp
  have hxhi := rev52_bound0_hi p hp
  by_cases h0 : p.1≤rev52_s0_lr.real.1
  · exact rev52_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev52_s1_lr.real.1
  · exact rev52_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev52_s2_lr.real.1
  · exact rev52_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev52_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull52 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,11,5,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow52 := by
  rw [← fractionRow52_correct]
  exact rev52_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull52
