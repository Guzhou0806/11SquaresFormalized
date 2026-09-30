import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks15
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev122_planes : List IntegerPlane := integerOverlayPlanes ![8,15,1,2]
def rev122_plane35 : IntegerPlane := ⟨(-15204000000),(-2139684000000),(-1570721771568)⟩
theorem rev122_plane35_mem : rev122_plane35 ∈ rev122_planes := by decide
def rev122_plane44 : IntegerPlane := ⟨699324000000,2145688000000,1695048727641⟩
theorem rev122_plane44_mem : rev122_plane44 ∈ rev122_planes := by decide
def rev122_plane67 : IntegerPlane := ⟨(-287616000000),1855520000000,1356143759600⟩
theorem rev122_plane67_mem : rev122_plane67 ∈ rev122_planes := by decide
def rev122_vertex0 : FractionPoint := fractionRow122[0]!
theorem rev122_vertex0_mem : rev122_vertex0∈fractionRow122 := by decide
def rev122_vertex1 : FractionPoint := fractionRow122[1]!
theorem rev122_vertex1_mem : rev122_vertex1∈fractionRow122 := by decide
def rev122_vertex2 : FractionPoint := fractionRow122[2]!
theorem rev122_vertex2_mem : rev122_vertex2∈fractionRow122 := by decide
def rev122_s0_ll : FractionPoint := ⟨13319330691551,670436124400000,351475835396027,478882946000000⟩
theorem rev122_s0_ll_mem : rev122_s0_ll.real ∈ rationalHull (fractionRow122.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow122 rev122_plane35 rev122_vertex0 rev122_vertex1 rev122_s0_ll
    rev122_vertex0_mem rev122_vertex1_mem (by decide)
def rev122_s0_lr : FractionPoint := ⟨1470846399148897,11967149176800000,7822791252895487089681,10669132341338388000000⟩
theorem rev122_s0_lr_mem : rev122_s0_lr.real ∈ rationalHull (fractionRow122.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow122 rev122_plane35 rev122_vertex0 rev122_vertex1 rev122_s0_lr
    rev122_vertex0_mem rev122_vertex1_mem (by decide)
def rev122_s0_ul : FractionPoint := ⟨13319330691551,670436124400000,351475835396027,478882946000000⟩
theorem rev122_s0_ul_mem : rev122_s0_ul.real ∈ rationalHull (fractionRow122.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow122 rev122_plane67 rev122_vertex0 rev122_vertex2 rev122_s0_ul
    rev122_vertex0_mem rev122_vertex2_mem (by decide)
def rev122_s0_ur : FractionPoint := ⟨1470846399148897,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev122_s0_ur_mem : rev122_s0_ur.real ∈ rationalHull (fractionRow122.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow122 rev122_plane67 rev122_vertex0 rev122_vertex2 rev122_s0_ur
    rev122_vertex0_mem rev122_vertex2_mem (by decide)
theorem rev122_slab0 (p : Point) (hp : p∈IntegerCarrier rev122_planes)
    (hx0 : rev122_s0_ll.real.1≤p.1) (hx1 : p.1≤rev122_s0_lr.real.1) :
    p∈rationalHull (fractionRow122.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev122_plane35 rev122_plane67 rev122_s0_ll rev122_s0_lr rev122_s0_ul rev122_s0_ur
    (by decide) rev122_s0_ll_mem rev122_s0_lr_mem rev122_s0_ul_mem rev122_s0_ur_mem p
    (hp _ rev122_plane35_mem) (hp _ rev122_plane67_mem) hx0 hx1
def rev122_s1_ll : FractionPoint := ⟨1470846399148897,11967149176800000,7822791252895487089681,10669132341338388000000⟩
theorem rev122_s1_ll_mem : rev122_s1_ll.real ∈ rationalHull (fractionRow122.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow122 rev122_plane35 rev122_vertex0 rev122_vertex1 rev122_s1_ll
    rev122_vertex0_mem rev122_vertex1_mem (by decide)
def rev122_s1_lr : FractionPoint := ⟨4276496419360111,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev122_s1_lr_mem : rev122_s1_lr.real ∈ rationalHull (fractionRow122.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow122 rev122_plane35 rev122_vertex0 rev122_vertex1 rev122_s1_lr
    rev122_vertex0_mem rev122_vertex1_mem (by decide)
def rev122_s1_ul : FractionPoint := ⟨1470846399148897,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev122_s1_ul_mem : rev122_s1_ul.real ∈ rationalHull (fractionRow122.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow122 rev122_plane44 rev122_vertex2 rev122_vertex1 rev122_s1_ul
    rev122_vertex2_mem rev122_vertex1_mem (by decide)
def rev122_s1_ur : FractionPoint := ⟨4276496419360111,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev122_s1_ur_mem : rev122_s1_ur.real ∈ rationalHull (fractionRow122.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow122 rev122_plane44 rev122_vertex2 rev122_vertex1 rev122_s1_ur
    rev122_vertex2_mem rev122_vertex1_mem (by decide)
theorem rev122_slab1 (p : Point) (hp : p∈IntegerCarrier rev122_planes)
    (hx0 : rev122_s1_ll.real.1≤p.1) (hx1 : p.1≤rev122_s1_lr.real.1) :
    p∈rationalHull (fractionRow122.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev122_plane35 rev122_plane44 rev122_s1_ll rev122_s1_lr rev122_s1_ul rev122_s1_ur
    (by decide) rev122_s1_ll_mem rev122_s1_lr_mem rev122_s1_ul_mem rev122_s1_ur_mem p
    (hp _ rev122_plane35_mem) (hp _ rev122_plane44_mem) hx0 hx1
theorem rev122_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev122_planes) : rev122_s0_ll.real.1≤p.1 := by
  have hc := rev122_plane35.combine_sound rev122_plane67 1855520000000 2139684000000 (by decide) (by decide) p
    (hp _ rev122_plane35_mem) (hp _ rev122_plane67_mem)
  exact (rev122_plane35.combine rev122_plane67 1855520000000 2139684000000).xBoundCheck_sound rev122_s0_ll.nx rev122_s0_ll.dx true (by decide) p hc
theorem rev122_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev122_planes) : p.1≤rev122_s1_lr.real.1 := by
  have hc := rev122_plane35.combine_sound rev122_plane44 2145688000000 2139684000000 (by decide) (by decide) p
    (hp _ rev122_plane35_mem) (hp _ rev122_plane44_mem)
  exact (rev122_plane35.combine rev122_plane44 2145688000000 2139684000000).xBoundCheck_sound rev122_s1_lr.nx rev122_s1_lr.dx false (by decide) p hc
theorem rev122_hull (p : Point) (hp : p∈IntegerCarrier rev122_planes) :
    p∈rationalHull (fractionRow122.map FractionPoint.rational) := by
  have hxlo := rev122_bound0_lo p hp
  have hxhi := rev122_bound0_hi p hp
  by_cases h0 : p.1≤rev122_s0_lr.real.1
  · exact rev122_slab0 p hp hxlo h0
  exact rev122_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull122 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,15,1,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow122 := by
  rw [← fractionRow122_correct]
  exact rev122_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull122
