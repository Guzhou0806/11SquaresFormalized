import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks3
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev24_planes : List IntegerPlane := integerOverlayPlanes ![2,1,15,8]
def rev24_plane7 : IntegerPlane := ⟨1855520000000,(-287616000000),1356143759600⟩
theorem rev24_plane7_mem : rev24_plane7 ∈ rev24_planes := by decide
def rev24_plane24 : IntegerPlane := ⟨2145688000000,699324000000,1695048727641⟩
theorem rev24_plane24_mem : rev24_plane24 ∈ rev24_planes := by decide
def rev24_plane55 : IntegerPlane := ⟨(-2139684000000),(-15204000000),(-1570721771568)⟩
theorem rev24_plane55_mem : rev24_plane55 ∈ rev24_planes := by decide
def rev24_vertex0 : FractionPoint := fractionRow24[0]!
theorem rev24_vertex0_mem : rev24_vertex0∈fractionRow24 := by decide
def rev24_vertex1 : FractionPoint := fractionRow24[1]!
theorem rev24_vertex1_mem : rev24_vertex1∈fractionRow24 := by decide
def rev24_vertex2 : FractionPoint := fractionRow24[2]!
theorem rev24_vertex2_mem : rev24_vertex2∈fractionRow24 := by decide
def rev24_s0_ll : FractionPoint := ⟨89389325943747189,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev24_s0_ll_mem : rev24_s0_ll.real ∈ rationalHull (fractionRow24.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow24 rev24_plane55 rev24_vertex2 rev24_vertex0 rev24_s0_ll
    rev24_vertex2_mem rev24_vertex0_mem (by decide)
def rev24_s0_lr : FractionPoint := ⟨351475835396027,478882946000000,13319330691551,670436124400000⟩
theorem rev24_s0_lr_mem : rev24_s0_lr.real ∈ rationalHull (fractionRow24.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow24 rev24_plane55 rev24_vertex2 rev24_vertex0 rev24_s0_lr
    rev24_vertex2_mem rev24_vertex0_mem (by decide)
def rev24_s0_ul : FractionPoint := ⟨89389325943747189,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev24_s0_ul_mem : rev24_s0_ul.real ∈ rationalHull (fractionRow24.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow24 rev24_plane24 rev24_vertex2 rev24_vertex1 rev24_s0_ul
    rev24_vertex2_mem rev24_vertex1_mem (by decide)
def rev24_s0_ur : FractionPoint := ⟨351475835396027,478882946000000,5757244600704332881,33489433732850400000⟩
theorem rev24_s0_ur_mem : rev24_s0_ur.real ∈ rationalHull (fractionRow24.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow24 rev24_plane24 rev24_vertex2 rev24_vertex1 rev24_s0_ur
    rev24_vertex2_mem rev24_vertex1_mem (by decide)
theorem rev24_slab0 (p : Point) (hp : p∈IntegerCarrier rev24_planes)
    (hx0 : rev24_s0_ll.real.1≤p.1) (hx1 : p.1≤rev24_s0_lr.real.1) :
    p∈rationalHull (fractionRow24.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev24_plane55 rev24_plane24 rev24_s0_ll rev24_s0_lr rev24_s0_ul rev24_s0_ur
    (by decide) rev24_s0_ll_mem rev24_s0_lr_mem rev24_s0_ul_mem rev24_s0_ur_mem p
    (hp _ rev24_plane55_mem) (hp _ rev24_plane24_mem) hx0 hx1
def rev24_s1_ll : FractionPoint := ⟨351475835396027,478882946000000,13319330691551,670436124400000⟩
theorem rev24_s1_ll_mem : rev24_s1_ll.real ∈ rationalHull (fractionRow24.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow24 rev24_plane7 rev24_vertex0 rev24_vertex1 rev24_s1_ll
    rev24_vertex0_mem rev24_vertex1_mem (by decide)
def rev24_s1_lr : FractionPoint := ⟨7478682361394293,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev24_s1_lr_mem : rev24_s1_lr.real ∈ rationalHull (fractionRow24.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow24 rev24_plane7 rev24_vertex0 rev24_vertex1 rev24_s1_lr
    rev24_vertex0_mem rev24_vertex1_mem (by decide)
def rev24_s1_ul : FractionPoint := ⟨351475835396027,478882946000000,5757244600704332881,33489433732850400000⟩
theorem rev24_s1_ul_mem : rev24_s1_ul.real ∈ rationalHull (fractionRow24.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow24 rev24_plane24 rev24_vertex2 rev24_vertex1 rev24_s1_ul
    rev24_vertex2_mem rev24_vertex1_mem (by decide)
def rev24_s1_ur : FractionPoint := ⟨7478682361394293,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev24_s1_ur_mem : rev24_s1_ur.real ∈ rationalHull (fractionRow24.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow24 rev24_plane24 rev24_vertex2 rev24_vertex1 rev24_s1_ur
    rev24_vertex2_mem rev24_vertex1_mem (by decide)
theorem rev24_slab1 (p : Point) (hp : p∈IntegerCarrier rev24_planes)
    (hx0 : rev24_s1_ll.real.1≤p.1) (hx1 : p.1≤rev24_s1_lr.real.1) :
    p∈rationalHull (fractionRow24.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev24_plane7 rev24_plane24 rev24_s1_ll rev24_s1_lr rev24_s1_ul rev24_s1_ur
    (by decide) rev24_s1_ll_mem rev24_s1_lr_mem rev24_s1_ul_mem rev24_s1_ur_mem p
    (hp _ rev24_plane7_mem) (hp _ rev24_plane24_mem) hx0 hx1
theorem rev24_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev24_planes) : rev24_s0_ll.real.1≤p.1 := by
  have hc := rev24_plane24.combine_sound rev24_plane55 15204000000 699324000000 (by decide) (by decide) p
    (hp _ rev24_plane24_mem) (hp _ rev24_plane55_mem)
  exact (rev24_plane24.combine rev24_plane55 15204000000 699324000000).xBoundCheck_sound rev24_s0_ll.nx rev24_s0_ll.dx true (by decide) p hc
theorem rev24_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev24_planes) : p.1≤rev24_s1_lr.real.1 := by
  have hc := rev24_plane7.combine_sound rev24_plane24 699324000000 287616000000 (by decide) (by decide) p
    (hp _ rev24_plane7_mem) (hp _ rev24_plane24_mem)
  exact (rev24_plane7.combine rev24_plane24 699324000000 287616000000).xBoundCheck_sound rev24_s1_lr.nx rev24_s1_lr.dx false (by decide) p hc
theorem rev24_hull (p : Point) (hp : p∈IntegerCarrier rev24_planes) :
    p∈rationalHull (fractionRow24.map FractionPoint.rational) := by
  have hxlo := rev24_bound0_lo p hp
  have hxhi := rev24_bound0_hi p hp
  by_cases h0 : p.1≤rev24_s0_lr.real.1
  · exact rev24_slab0 p hp hxlo h0
  exact rev24_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull24 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,1,15,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow24 := by
  rw [← fractionRow24_correct]
  exact rev24_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull24
