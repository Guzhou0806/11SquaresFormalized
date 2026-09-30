import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks0
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev5_planes : List IntegerPlane := integerOverlayPlanes ![0,7,2,1]
def rev5_plane8 : IntegerPlane := ⟨(-15204000000),2139684000000,568962228432⟩
theorem rev5_plane8_mem : rev5_plane8 ∈ rev5_planes := by decide
def rev5_plane47 : IntegerPlane := ⟨(-287616000000),(-1855520000000),(-499376240400)⟩
theorem rev5_plane47_mem : rev5_plane47 ∈ rev5_planes := by decide
def rev5_plane64 : IntegerPlane := ⟨699324000000,(-2145688000000),(-450639272359)⟩
theorem rev5_plane64_mem : rev5_plane64 ∈ rev5_planes := by decide
def rev5_vertex0 : FractionPoint := fractionRow5[0]!
theorem rev5_vertex0_mem : rev5_vertex0∈fractionRow5 := by decide
def rev5_vertex1 : FractionPoint := fractionRow5[1]!
theorem rev5_vertex1_mem : rev5_vertex1∈fractionRow5 := by decide
def rev5_vertex2 : FractionPoint := fractionRow5[2]!
theorem rev5_vertex2_mem : rev5_vertex2∈fractionRow5 := by decide
def rev5_s0_ll : FractionPoint := ⟨13319330691551,670436124400000,127407110603973,478882946000000⟩
theorem rev5_s0_ll_mem : rev5_s0_ll.real ∈ rationalHull (fractionRow5.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow5 rev5_plane47 rev5_vertex1 rev5_vertex2 rev5_s0_ll
    rev5_vertex1_mem rev5_vertex2_mem (by decide)
def rev5_s0_lr : FractionPoint := ⟨1470846399148897,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev5_s0_lr_mem : rev5_s0_lr.real ∈ rationalHull (fractionRow5.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow5 rev5_plane47 rev5_vertex1 rev5_vertex2 rev5_s0_lr
    rev5_vertex1_mem rev5_vertex2_mem (by decide)
def rev5_s0_ul : FractionPoint := ⟨13319330691551,670436124400000,127407110603973,478882946000000⟩
theorem rev5_s0_ul_mem : rev5_s0_ul.real ∈ rationalHull (fractionRow5.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow5 rev5_plane8 rev5_vertex1 rev5_vertex0 rev5_s0_ul
    rev5_vertex1_mem rev5_vertex0_mem (by decide)
def rev5_s0_ur : FractionPoint := ⟨1470846399148897,11967149176800000,2846341088442900910319,10669132341338388000000⟩
theorem rev5_s0_ur_mem : rev5_s0_ur.real ∈ rationalHull (fractionRow5.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow5 rev5_plane8 rev5_vertex1 rev5_vertex0 rev5_s0_ur
    rev5_vertex1_mem rev5_vertex0_mem (by decide)
theorem rev5_slab0 (p : Point) (hp : p∈IntegerCarrier rev5_planes)
    (hx0 : rev5_s0_ll.real.1≤p.1) (hx1 : p.1≤rev5_s0_lr.real.1) :
    p∈rationalHull (fractionRow5.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev5_plane47 rev5_plane8 rev5_s0_ll rev5_s0_lr rev5_s0_ul rev5_s0_ur
    (by decide) rev5_s0_ll_mem rev5_s0_lr_mem rev5_s0_ul_mem rev5_s0_ur_mem p
    (hp _ rev5_plane47_mem) (hp _ rev5_plane8_mem) hx0 hx1
def rev5_s1_ll : FractionPoint := ⟨1470846399148897,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev5_s1_ll_mem : rev5_s1_ll.real ∈ rationalHull (fractionRow5.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow5 rev5_plane64 rev5_vertex2 rev5_vertex0 rev5_s1_ll
    rev5_vertex2_mem rev5_vertex0_mem (by decide)
def rev5_s1_lr : FractionPoint := ⟨4276496419360111,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev5_s1_lr_mem : rev5_s1_lr.real ∈ rationalHull (fractionRow5.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow5 rev5_plane64 rev5_vertex2 rev5_vertex0 rev5_s1_lr
    rev5_vertex2_mem rev5_vertex0_mem (by decide)
def rev5_s1_ul : FractionPoint := ⟨1470846399148897,11967149176800000,2846341088442900910319,10669132341338388000000⟩
theorem rev5_s1_ul_mem : rev5_s1_ul.real ∈ rationalHull (fractionRow5.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow5 rev5_plane8 rev5_vertex1 rev5_vertex0 rev5_s1_ul
    rev5_vertex1_mem rev5_vertex0_mem (by decide)
def rev5_s1_ur : FractionPoint := ⟨4276496419360111,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev5_s1_ur_mem : rev5_s1_ur.real ∈ rationalHull (fractionRow5.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow5 rev5_plane8 rev5_vertex1 rev5_vertex0 rev5_s1_ur
    rev5_vertex1_mem rev5_vertex0_mem (by decide)
theorem rev5_slab1 (p : Point) (hp : p∈IntegerCarrier rev5_planes)
    (hx0 : rev5_s1_ll.real.1≤p.1) (hx1 : p.1≤rev5_s1_lr.real.1) :
    p∈rationalHull (fractionRow5.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev5_plane64 rev5_plane8 rev5_s1_ll rev5_s1_lr rev5_s1_ul rev5_s1_ur
    (by decide) rev5_s1_ll_mem rev5_s1_lr_mem rev5_s1_ul_mem rev5_s1_ur_mem p
    (hp _ rev5_plane64_mem) (hp _ rev5_plane8_mem) hx0 hx1
theorem rev5_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev5_planes) : rev5_s0_ll.real.1≤p.1 := by
  have hc := rev5_plane8.combine_sound rev5_plane47 1855520000000 2139684000000 (by decide) (by decide) p
    (hp _ rev5_plane8_mem) (hp _ rev5_plane47_mem)
  exact (rev5_plane8.combine rev5_plane47 1855520000000 2139684000000).xBoundCheck_sound rev5_s0_ll.nx rev5_s0_ll.dx true (by decide) p hc
theorem rev5_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev5_planes) : p.1≤rev5_s1_lr.real.1 := by
  have hc := rev5_plane8.combine_sound rev5_plane64 2145688000000 2139684000000 (by decide) (by decide) p
    (hp _ rev5_plane8_mem) (hp _ rev5_plane64_mem)
  exact (rev5_plane8.combine rev5_plane64 2145688000000 2139684000000).xBoundCheck_sound rev5_s1_lr.nx rev5_s1_lr.dx false (by decide) p hc
theorem rev5_hull (p : Point) (hp : p∈IntegerCarrier rev5_planes) :
    p∈rationalHull (fractionRow5.map FractionPoint.rational) := by
  have hxlo := rev5_bound0_lo p hp
  have hxhi := rev5_bound0_hi p hp
  by_cases h0 : p.1≤rev5_s0_lr.real.1
  · exact rev5_slab0 p hp hxlo h0
  exact rev5_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull5 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,7,2,1] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow5 := by
  rw [← fractionRow5_correct]
  exact rev5_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull5
