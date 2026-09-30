import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks2
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev22_planes : List IntegerPlane := integerOverlayPlanes ![2,1,11,4]
def rev22_plane5 : IntegerPlane := ⟨(-2083356000000),(-746024000000),(-1117516707941)⟩
theorem rev22_plane5_mem : rev22_plane5 ∈ rev22_planes := by decide
def rev22_plane26 : IntegerPlane := ⟨(-2083356000000),746024000000,(-965839292059)⟩
theorem rev22_plane26_mem : rev22_plane26 ∈ rev22_planes := by decide
def rev22_plane29 : IntegerPlane := ⟨16372000000,2139440000000,393704847425⟩
theorem rev22_plane29_mem : rev22_plane29 ∈ rev22_planes := by decide
def rev22_plane72 : IntegerPlane := ⟨2112760000000,48252000000,1130009250915⟩
theorem rev22_plane72_mem : rev22_plane72 ∈ rev22_planes := by decide
def rev22_vertex0 : FractionPoint := fractionRow22[0]!
theorem rev22_vertex0_mem : rev22_vertex0∈fractionRow22 := by decide
def rev22_vertex1 : FractionPoint := fractionRow22[1]!
theorem rev22_vertex1_mem : rev22_vertex1∈fractionRow22 := by decide
def rev22_vertex2 : FractionPoint := fractionRow22[2]!
theorem rev22_vertex2_mem : rev22_vertex2∈fractionRow22 := by decide
def rev22_vertex3 : FractionPoint := fractionRow22[3]!
theorem rev22_vertex3_mem : rev22_vertex3∈fractionRow22 := by decide
def rev22_s0_ll : FractionPoint := ⟨1,2,75838707941,746024000000⟩
theorem rev22_s0_ll_mem : rev22_s0_ll.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane5 rev22_vertex2 rev22_vertex3 rev22_s0_ll
    rev22_vertex2_mem rev22_vertex3_mem (by decide)
def rev22_s0_lr : FractionPoint := ⟨59001712002452379,111735726639200000,1215606676658188361227,52098458581426588000000⟩
theorem rev22_s0_lr_mem : rev22_s0_lr.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane5 rev22_vertex2 rev22_vertex3 rev22_s0_lr
    rev22_vertex2_mem rev22_vertex3_mem (by decide)
def rev22_s0_ul : FractionPoint := ⟨1,2,75838707941,746024000000⟩
theorem rev22_s0_ul_mem : rev22_s0_ul.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane26 rev22_vertex2 rev22_vertex1 rev22_s0_ul
    rev22_vertex2_mem rev22_vertex1_mem (by decide)
def rev22_s0_ur : FractionPoint := ⟨59001712002452379,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev22_s0_ur_mem : rev22_s0_ur.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane26 rev22_vertex2 rev22_vertex1 rev22_s0_ur
    rev22_vertex2_mem rev22_vertex1_mem (by decide)
theorem rev22_slab0 (p : Point) (hp : p∈IntegerCarrier rev22_planes)
    (hx0 : rev22_s0_ll.real.1≤p.1) (hx1 : p.1≤rev22_s0_lr.real.1) :
    p∈rationalHull (fractionRow22.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev22_plane5 rev22_plane26 rev22_s0_ll rev22_s0_lr rev22_s0_ul rev22_s0_ur
    (by decide) rev22_s0_ll_mem rev22_s0_lr_mem rev22_s0_ul_mem rev22_s0_ur_mem p
    (hp _ rev22_plane5_mem) (hp _ rev22_plane26_mem) hx0 hx1
def rev22_s1_ll : FractionPoint := ⟨59001712002452379,111735726639200000,1215606676658188361227,52098458581426588000000⟩
theorem rev22_s1_ll_mem : rev22_s1_ll.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane5 rev22_vertex2 rev22_vertex3 rev22_s1_ll
    rev22_vertex2_mem rev22_vertex3_mem (by decide)
def rev22_s1_lr : FractionPoint := ⟨4797179890959273,9038666545312000,1666052702877665414603,105360346418747492000000⟩
theorem rev22_s1_lr_mem : rev22_s1_lr.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane5 rev22_vertex2 rev22_vertex3 rev22_s1_lr
    rev22_vertex2_mem rev22_vertex3_mem (by decide)
def rev22_s1_ul : FractionPoint := ⟨59001712002452379,111735726639200000,25137957350699011,139669658299000000⟩
theorem rev22_s1_ul_mem : rev22_s1_ul.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane29 rev22_vertex1 rev22_vertex0 rev22_s1_ul
    rev22_vertex1_mem rev22_vertex0_mem (by decide)
def rev22_s1_ur : FractionPoint := ⟨4797179890959273,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev22_s1_ur_mem : rev22_s1_ur.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane29 rev22_vertex1 rev22_vertex0 rev22_s1_ur
    rev22_vertex1_mem rev22_vertex0_mem (by decide)
theorem rev22_slab1 (p : Point) (hp : p∈IntegerCarrier rev22_planes)
    (hx0 : rev22_s1_ll.real.1≤p.1) (hx1 : p.1≤rev22_s1_lr.real.1) :
    p∈rationalHull (fractionRow22.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev22_plane5 rev22_plane29 rev22_s1_ll rev22_s1_lr rev22_s1_ul rev22_s1_ur
    (by decide) rev22_s1_ll_mem rev22_s1_lr_mem rev22_s1_ul_mem rev22_s1_ur_mem p
    (hp _ rev22_plane5_mem) (hp _ rev22_plane29_mem) hx0 hx1
def rev22_s2_ll : FractionPoint := ⟨4797179890959273,9038666545312000,1666052702877665414603,105360346418747492000000⟩
theorem rev22_s2_ll_mem : rev22_s2_ll.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane5 rev22_vertex2 rev22_vertex3 rev22_s2_ll
    rev22_vertex2_mem rev22_vertex3_mem (by decide)
def rev22_s2_lr : FractionPoint := ⟨197272901303260707,368910893132000000,341652346007821,73782178626400000⟩
theorem rev22_s2_lr_mem : rev22_s2_lr.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane5 rev22_vertex2 rev22_vertex3 rev22_s2_lr
    rev22_vertex2_mem rev22_vertex3_mem (by decide)
def rev22_s2_ul : FractionPoint := ⟨4797179890959273,9038666545312000,40665167099483131,225966663632800000⟩
theorem rev22_s2_ul_mem : rev22_s2_ul.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane72 rev22_vertex0 rev22_vertex3 rev22_s2_ul
    rev22_vertex0_mem rev22_vertex3_mem (by decide)
def rev22_s2_ur : FractionPoint := ⟨197272901303260707,368910893132000000,341652346007821,73782178626400000⟩
theorem rev22_s2_ur_mem : rev22_s2_ur.real ∈ rationalHull (fractionRow22.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow22 rev22_plane72 rev22_vertex0 rev22_vertex3 rev22_s2_ur
    rev22_vertex0_mem rev22_vertex3_mem (by decide)
theorem rev22_slab2 (p : Point) (hp : p∈IntegerCarrier rev22_planes)
    (hx0 : rev22_s2_ll.real.1≤p.1) (hx1 : p.1≤rev22_s2_lr.real.1) :
    p∈rationalHull (fractionRow22.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev22_plane5 rev22_plane72 rev22_s2_ll rev22_s2_lr rev22_s2_ul rev22_s2_ur
    (by decide) rev22_s2_ll_mem rev22_s2_lr_mem rev22_s2_ul_mem rev22_s2_ur_mem p
    (hp _ rev22_plane5_mem) (hp _ rev22_plane72_mem) hx0 hx1
theorem rev22_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev22_planes) : rev22_s0_ll.real.1≤p.1 := by
  have hc := rev22_plane5.combine_sound rev22_plane26 746024000000 746024000000 (by decide) (by decide) p
    (hp _ rev22_plane5_mem) (hp _ rev22_plane26_mem)
  exact (rev22_plane5.combine rev22_plane26 746024000000 746024000000).xBoundCheck_sound rev22_s0_ll.nx rev22_s0_ll.dx true (by decide) p hc
theorem rev22_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev22_planes) : p.1≤rev22_s2_lr.real.1 := by
  have hc := rev22_plane5.combine_sound rev22_plane72 48252000000 746024000000 (by decide) (by decide) p
    (hp _ rev22_plane5_mem) (hp _ rev22_plane72_mem)
  exact (rev22_plane5.combine rev22_plane72 48252000000 746024000000).xBoundCheck_sound rev22_s2_lr.nx rev22_s2_lr.dx false (by decide) p hc
theorem rev22_hull (p : Point) (hp : p∈IntegerCarrier rev22_planes) :
    p∈rationalHull (fractionRow22.map FractionPoint.rational) := by
  have hxlo := rev22_bound0_lo p hp
  have hxhi := rev22_bound0_hi p hp
  by_cases h0 : p.1≤rev22_s0_lr.real.1
  · exact rev22_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev22_s1_lr.real.1
  · exact rev22_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev22_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull22 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,1,11,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow22 := by
  rw [← fractionRow22_correct]
  exact rev22_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull22
