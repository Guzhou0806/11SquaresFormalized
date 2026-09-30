import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks21
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev168_planes : List IntegerPlane := integerOverlayPlanes ![11,4,13,10]
def rev168_plane32 : IntegerPlane := ⟨(-48252000000),2112760000000,1081757250915⟩
theorem rev168_plane32_mem : rev168_plane32 ∈ rev168_planes := by decide
def rev168_plane33 : IntegerPlane := ⟨(-2093220000000),1468788000000,(-880675273104)⟩
theorem rev168_plane33_mem : rev168_plane33 ∈ rev168_planes := by decide
def rev168_plane54 : IntegerPlane := ⟨(-1393416000000),(-2099728000000),(-2133599860516)⟩
theorem rev168_plane54_mem : rev168_plane54 ∈ rev168_planes := by decide
def rev168_plane77 : IntegerPlane := ⟨1393416000000,(-2099728000000),33871860516⟩
theorem rev168_plane77_mem : rev168_plane77 ∈ rev168_planes := by decide
def rev168_plane78 : IntegerPlane := ⟨2139440000000,(-16372000000),1745735152575⟩
theorem rev168_plane78_mem : rev168_plane78 ∈ rev168_planes := by decide
def rev168_vertex0 : FractionPoint := fractionRow168[0]!
theorem rev168_vertex0_mem : rev168_vertex0∈fractionRow168 := by decide
def rev168_vertex1 : FractionPoint := fractionRow168[1]!
theorem rev168_vertex1_mem : rev168_vertex1∈fractionRow168 := by decide
def rev168_vertex2 : FractionPoint := fractionRow168[2]!
theorem rev168_vertex2_mem : rev168_vertex2∈fractionRow168 := by decide
def rev168_vertex3 : FractionPoint := fractionRow168[3]!
theorem rev168_vertex3_mem : rev168_vertex3∈fractionRow168 := by decide
def rev168_vertex4 : FractionPoint := fractionRow168[4]!
theorem rev168_vertex4_mem : rev168_vertex4∈fractionRow168 := by decide
def rev168_s0_ll : FractionPoint := ⟨20762435007382043,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev168_s0_ll_mem : rev168_s0_ll.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane54 rev168_vertex2 rev168_vertex3 rev168_s0_ll
    rev168_vertex2_mem rev168_vertex3_mem (by decide)
def rev168_s0_lr : FractionPoint := ⟨270933965129,348354000000,1,2⟩
theorem rev168_s0_lr_mem : rev168_s0_lr.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane54 rev168_vertex2 rev168_vertex3 rev168_s0_lr
    rev168_vertex2_mem rev168_vertex3_mem (by decide)
def rev168_s0_ul : FractionPoint := ⟨20762435007382043,26840938933200000,22492686692234849,44734898222000000⟩
theorem rev168_s0_ul_mem : rev168_s0_ul.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane33 rev168_vertex2 rev168_vertex1 rev168_s0_ul
    rev168_vertex2_mem rev168_vertex1_mem (by decide)
def rev168_s0_ur : FractionPoint := ⟨270933965129,348354000000,7231601122234849,14212727082000000⟩
theorem rev168_s0_ur_mem : rev168_s0_ur.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane33 rev168_vertex2 rev168_vertex1 rev168_s0_ur
    rev168_vertex2_mem rev168_vertex1_mem (by decide)
theorem rev168_slab0 (p : Point) (hp : p∈IntegerCarrier rev168_planes)
    (hx0 : rev168_s0_ll.real.1≤p.1) (hx1 : p.1≤rev168_s0_lr.real.1) :
    p∈rationalHull (fractionRow168.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev168_plane54 rev168_plane33 rev168_s0_ll rev168_s0_lr rev168_s0_ul rev168_s0_ur
    (by decide) rev168_s0_ll_mem rev168_s0_lr_mem rev168_s0_ul_mem rev168_s0_ur_mem p
    (hp _ rev168_plane54_mem) (hp _ rev168_plane33_mem) hx0 hx1
def rev168_s1_ll : FractionPoint := ⟨270933965129,348354000000,1,2⟩
theorem rev168_s1_ll_mem : rev168_s1_ll.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane77 rev168_vertex3 rev168_vertex4 rev168_s1_ll
    rev168_vertex3_mem rev168_vertex4_mem (by decide)
def rev168_s1_lr : FractionPoint := ⟨57492125984335801,72526658810400000,5392627454838323833059,10575434461850248000000⟩
theorem rev168_s1_lr_mem : rev168_s1_lr.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane77 rev168_vertex3 rev168_vertex4 rev168_s1_lr
    rev168_vertex3_mem rev168_vertex4_mem (by decide)
def rev168_s1_ul : FractionPoint := ⟨270933965129,348354000000,7231601122234849,14212727082000000⟩
theorem rev168_s1_ul_mem : rev168_s1_ul.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane33 rev168_vertex2 rev168_vertex1 rev168_s1_ul
    rev168_vertex2_mem rev168_vertex1_mem (by decide)
def rev168_s1_ur : FractionPoint := ⟨57492125984335801,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev168_s1_ur_mem : rev168_s1_ur.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane33 rev168_vertex2 rev168_vertex1 rev168_s1_ur
    rev168_vertex2_mem rev168_vertex1_mem (by decide)
theorem rev168_slab1 (p : Point) (hp : p∈IntegerCarrier rev168_planes)
    (hx0 : rev168_s1_ll.real.1≤p.1) (hx1 : p.1≤rev168_s1_lr.real.1) :
    p∈rationalHull (fractionRow168.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev168_plane77 rev168_plane33 rev168_s1_ll rev168_s1_lr rev168_s1_ul rev168_s1_ur
    (by decide) rev168_s1_ll_mem rev168_s1_lr_mem rev168_s1_ul_mem rev168_s1_ur_mem p
    (hp _ rev168_plane77_mem) (hp _ rev168_plane33_mem) hx0 hx1
def rev168_s2_ll : FractionPoint := ⟨57492125984335801,72526658810400000,5392627454838323833059,10575434461850248000000⟩
theorem rev168_s2_ll_mem : rev168_s2_ll.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane77 rev168_vertex3 rev168_vertex4 rev168_s2_ll
    rev168_vertex3_mem rev168_vertex4_mem (by decide)
def rev168_s2_lr : FractionPoint := ⟨114531700948300989,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev168_s2_lr_mem : rev168_s2_lr.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane77 rev168_vertex3 rev168_vertex4 rev168_s2_lr
    rev168_vertex3_mem rev168_vertex4_mem (by decide)
def rev168_s2_ul : FractionPoint := ⟨57492125984335801,72526658810400000,64079173778836403,120877764684000000⟩
theorem rev168_s2_ul_mem : rev168_s2_ul.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane32 rev168_vertex1 rev168_vertex0 rev168_s2_ul
    rev168_vertex1_mem rev168_vertex0_mem (by decide)
def rev168_s2_ur : FractionPoint := ⟨114531700948300989,139669658299000000,156615049231921074414813,295088467267795240000000⟩
theorem rev168_s2_ur_mem : rev168_s2_ur.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane32 rev168_vertex1 rev168_vertex0 rev168_s2_ur
    rev168_vertex1_mem rev168_vertex0_mem (by decide)
theorem rev168_slab2 (p : Point) (hp : p∈IntegerCarrier rev168_planes)
    (hx0 : rev168_s2_ll.real.1≤p.1) (hx1 : p.1≤rev168_s2_lr.real.1) :
    p∈rationalHull (fractionRow168.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev168_plane77 rev168_plane32 rev168_s2_ll rev168_s2_lr rev168_s2_ul rev168_s2_ur
    (by decide) rev168_s2_ll_mem rev168_s2_lr_mem rev168_s2_ul_mem rev168_s2_ur_mem p
    (hp _ rev168_plane77_mem) (hp _ rev168_plane32_mem) hx0 hx1
def rev168_s3_ll : FractionPoint := ⟨114531700948300989,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev168_s3_ll_mem : rev168_s3_ll.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane78 rev168_vertex4 rev168_vertex0 rev168_s3_ll
    rev168_vertex4_mem rev168_vertex0_mem (by decide)
def rev168_s3_lr : FractionPoint := ⟨185301496533316869,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev168_s3_lr_mem : rev168_s3_lr.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane78 rev168_vertex4 rev168_vertex0 rev168_s3_lr
    rev168_vertex4_mem rev168_vertex0_mem (by decide)
def rev168_s3_ul : FractionPoint := ⟨114531700948300989,139669658299000000,156615049231921074414813,295088467267795240000000⟩
theorem rev168_s3_ul_mem : rev168_s3_ul.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane32 rev168_vertex1 rev168_vertex0 rev168_s3_ul
    rev168_vertex1_mem rev168_vertex0_mem (by decide)
def rev168_s3_ur : FractionPoint := ⟨185301496533316869,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev168_s3_ur_mem : rev168_s3_ur.real ∈ rationalHull (fractionRow168.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow168 rev168_plane32 rev168_vertex1 rev168_vertex0 rev168_s3_ur
    rev168_vertex1_mem rev168_vertex0_mem (by decide)
theorem rev168_slab3 (p : Point) (hp : p∈IntegerCarrier rev168_planes)
    (hx0 : rev168_s3_ll.real.1≤p.1) (hx1 : p.1≤rev168_s3_lr.real.1) :
    p∈rationalHull (fractionRow168.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev168_plane78 rev168_plane32 rev168_s3_ll rev168_s3_lr rev168_s3_ul rev168_s3_ur
    (by decide) rev168_s3_ll_mem rev168_s3_lr_mem rev168_s3_ul_mem rev168_s3_ur_mem p
    (hp _ rev168_plane78_mem) (hp _ rev168_plane32_mem) hx0 hx1
theorem rev168_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev168_planes) : rev168_s0_ll.real.1≤p.1 := by
  have hc := rev168_plane33.combine_sound rev168_plane54 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev168_plane33_mem) (hp _ rev168_plane54_mem)
  exact (rev168_plane33.combine rev168_plane54 2099728000000 1468788000000).xBoundCheck_sound rev168_s0_ll.nx rev168_s0_ll.dx true (by decide) p hc
theorem rev168_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev168_planes) : p.1≤rev168_s3_lr.real.1 := by
  have hc := rev168_plane32.combine_sound rev168_plane78 16372000000 2112760000000 (by decide) (by decide) p
    (hp _ rev168_plane32_mem) (hp _ rev168_plane78_mem)
  exact (rev168_plane32.combine rev168_plane78 16372000000 2112760000000).xBoundCheck_sound rev168_s3_lr.nx rev168_s3_lr.dx false (by decide) p hc
theorem rev168_hull (p : Point) (hp : p∈IntegerCarrier rev168_planes) :
    p∈rationalHull (fractionRow168.map FractionPoint.rational) := by
  have hxlo := rev168_bound0_lo p hp
  have hxhi := rev168_bound0_hi p hp
  by_cases h0 : p.1≤rev168_s0_lr.real.1
  · exact rev168_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev168_s1_lr.real.1
  · exact rev168_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev168_s2_lr.real.1
  · exact rev168_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev168_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull168 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,4,13,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow168 := by
  rw [← fractionRow168_correct]
  exact rev168_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull168
