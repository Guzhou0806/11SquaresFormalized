import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks6
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev48_planes : List IntegerPlane := integerOverlayPlanes ![4,11,1,2]
def rev48_plane12 : IntegerPlane := ⟨48252000000,2112760000000,1130009250915⟩
theorem rev48_plane12_mem : rev48_plane12 ∈ rev48_planes := by decide
def rev48_plane46 : IntegerPlane := ⟨746024000000,(-2083356000000),(-965839292059)⟩
theorem rev48_plane46_mem : rev48_plane46 ∈ rev48_planes := by decide
def rev48_plane49 : IntegerPlane := ⟨2139440000000,16372000000,393704847425⟩
theorem rev48_plane49_mem : rev48_plane49 ∈ rev48_planes := by decide
def rev48_plane65 : IntegerPlane := ⟨(-746024000000),(-2083356000000),(-1117516707941)⟩
theorem rev48_plane65_mem : rev48_plane65 ∈ rev48_planes := by decide
def rev48_vertex0 : FractionPoint := fractionRow48[0]!
theorem rev48_vertex0_mem : rev48_vertex0∈fractionRow48 := by decide
def rev48_vertex1 : FractionPoint := fractionRow48[1]!
theorem rev48_vertex1_mem : rev48_vertex1∈fractionRow48 := by decide
def rev48_vertex2 : FractionPoint := fractionRow48[2]!
theorem rev48_vertex2_mem : rev48_vertex2∈fractionRow48 := by decide
def rev48_vertex3 : FractionPoint := fractionRow48[3]!
theorem rev48_vertex3_mem : rev48_vertex3∈fractionRow48 := by decide
def rev48_s0_ll : FractionPoint := ⟨341652346007821,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev48_s0_ll_mem : rev48_s0_ll.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane65 rev48_vertex3 rev48_vertex0 rev48_s0_ll
    rev48_vertex3_mem rev48_vertex0_mem (by decide)
def rev48_s0_lr : FractionPoint := ⟨75838707941,746024000000,1,2⟩
theorem rev48_s0_lr_mem : rev48_s0_lr.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane65 rev48_vertex3 rev48_vertex0 rev48_s0_lr
    rev48_vertex3_mem rev48_vertex0_mem (by decide)
def rev48_s0_ul : FractionPoint := ⟨341652346007821,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev48_s0_ul_mem : rev48_s0_ul.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane12 rev48_vertex3 rev48_vertex2 rev48_s0_ul
    rev48_vertex3_mem rev48_vertex2_mem (by decide)
def rev48_s0_ur : FractionPoint := ⟨75838707941,746024000000,209838663017260707,394042416560000000⟩
theorem rev48_s0_ur_mem : rev48_s0_ur.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane12 rev48_vertex3 rev48_vertex2 rev48_s0_ur
    rev48_vertex3_mem rev48_vertex2_mem (by decide)
theorem rev48_slab0 (p : Point) (hp : p∈IntegerCarrier rev48_planes)
    (hx0 : rev48_s0_ll.real.1≤p.1) (hx1 : p.1≤rev48_s0_lr.real.1) :
    p∈rationalHull (fractionRow48.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev48_plane65 rev48_plane12 rev48_s0_ll rev48_s0_lr rev48_s0_ul rev48_s0_ur
    (by decide) rev48_s0_ll_mem rev48_s0_lr_mem rev48_s0_ul_mem rev48_s0_ur_mem p
    (hp _ rev48_plane65_mem) (hp _ rev48_plane12_mem) hx0 hx1
def rev48_s1_ll : FractionPoint := ⟨75838707941,746024000000,1,2⟩
theorem rev48_s1_ll_mem : rev48_s1_ll.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane46 rev48_vertex0 rev48_vertex1 rev48_s1_ll
    rev48_vertex0_mem rev48_vertex1_mem (by decide)
def rev48_s1_lr : FractionPoint := ⟨40665167099483131,225966663632800000,34525649035036463396261,65384583955468844000000⟩
theorem rev48_s1_lr_mem : rev48_s1_lr.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane46 rev48_vertex0 rev48_vertex1 rev48_s1_lr
    rev48_vertex0_mem rev48_vertex1_mem (by decide)
def rev48_s1_ul : FractionPoint := ⟨75838707941,746024000000,209838663017260707,394042416560000000⟩
theorem rev48_s1_ul_mem : rev48_s1_ul.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane12 rev48_vertex3 rev48_vertex2 rev48_s1_ul
    rev48_vertex3_mem rev48_vertex2_mem (by decide)
def rev48_s1_ur : FractionPoint := ⟨40665167099483131,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev48_s1_ur_mem : rev48_s1_ur.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane12 rev48_vertex3 rev48_vertex2 rev48_s1_ur
    rev48_vertex3_mem rev48_vertex2_mem (by decide)
theorem rev48_slab1 (p : Point) (hp : p∈IntegerCarrier rev48_planes)
    (hx0 : rev48_s1_ll.real.1≤p.1) (hx1 : p.1≤rev48_s1_lr.real.1) :
    p∈rationalHull (fractionRow48.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev48_plane46 rev48_plane12 rev48_s1_ll rev48_s1_lr rev48_s1_ul rev48_s1_ur
    (by decide) rev48_s1_ll_mem rev48_s1_lr_mem rev48_s1_ul_mem rev48_s1_ur_mem p
    (hp _ rev48_plane46_mem) (hp _ rev48_plane12_mem) hx0 hx1
def rev48_s2_ll : FractionPoint := ⟨40665167099483131,225966663632800000,34525649035036463396261,65384583955468844000000⟩
theorem rev48_s2_ll_mem : rev48_s2_ll.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane46 rev48_vertex0 rev48_vertex1 rev48_s2_ll
    rev48_vertex0_mem rev48_vertex1_mem (by decide)
def rev48_s2_lr : FractionPoint := ⟨25137957350699011,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev48_s2_lr_mem : rev48_s2_lr.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane46 rev48_vertex0 rev48_vertex1 rev48_s2_lr
    rev48_vertex0_mem rev48_vertex1_mem (by decide)
def rev48_s2_ul : FractionPoint := ⟨40665167099483131,225966663632800000,4797179890959273,9038666545312000⟩
theorem rev48_s2_ul_mem : rev48_s2_ul.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane49 rev48_vertex2 rev48_vertex1 rev48_s2_ul
    rev48_vertex2_mem rev48_vertex1_mem (by decide)
def rev48_s2_ur : FractionPoint := ⟨25137957350699011,139669658299000000,59001712002452379,111735726639200000⟩
theorem rev48_s2_ur_mem : rev48_s2_ur.real ∈ rationalHull (fractionRow48.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow48 rev48_plane49 rev48_vertex2 rev48_vertex1 rev48_s2_ur
    rev48_vertex2_mem rev48_vertex1_mem (by decide)
theorem rev48_slab2 (p : Point) (hp : p∈IntegerCarrier rev48_planes)
    (hx0 : rev48_s2_ll.real.1≤p.1) (hx1 : p.1≤rev48_s2_lr.real.1) :
    p∈rationalHull (fractionRow48.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev48_plane46 rev48_plane49 rev48_s2_ll rev48_s2_lr rev48_s2_ul rev48_s2_ur
    (by decide) rev48_s2_ll_mem rev48_s2_lr_mem rev48_s2_ul_mem rev48_s2_ur_mem p
    (hp _ rev48_plane46_mem) (hp _ rev48_plane49_mem) hx0 hx1
theorem rev48_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev48_planes) : rev48_s0_ll.real.1≤p.1 := by
  have hc := rev48_plane12.combine_sound rev48_plane65 2083356000000 2112760000000 (by decide) (by decide) p
    (hp _ rev48_plane12_mem) (hp _ rev48_plane65_mem)
  exact (rev48_plane12.combine rev48_plane65 2083356000000 2112760000000).xBoundCheck_sound rev48_s0_ll.nx rev48_s0_ll.dx true (by decide) p hc
theorem rev48_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev48_planes) : p.1≤rev48_s2_lr.real.1 := by
  have hc := rev48_plane46.combine_sound rev48_plane49 16372000000 2083356000000 (by decide) (by decide) p
    (hp _ rev48_plane46_mem) (hp _ rev48_plane49_mem)
  exact (rev48_plane46.combine rev48_plane49 16372000000 2083356000000).xBoundCheck_sound rev48_s2_lr.nx rev48_s2_lr.dx false (by decide) p hc
theorem rev48_hull (p : Point) (hp : p∈IntegerCarrier rev48_planes) :
    p∈rationalHull (fractionRow48.map FractionPoint.rational) := by
  have hxlo := rev48_bound0_lo p hp
  have hxhi := rev48_bound0_hi p hp
  by_cases h0 : p.1≤rev48_s0_lr.real.1
  · exact rev48_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev48_s1_lr.real.1
  · exact rev48_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev48_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull48 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,11,1,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow48 := by
  rw [← fractionRow48_correct]
  exact rev48_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull48
