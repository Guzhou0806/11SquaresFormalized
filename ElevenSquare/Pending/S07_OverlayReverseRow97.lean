import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks12
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev97_planes : List IntegerPlane := integerOverlayPlanes ![7,0,14,13]
def rev97_plane28 : IntegerPlane := ⟨15204000000,2139684000000,584166228432⟩
theorem rev97_plane28_mem : rev97_plane28 ∈ rev97_planes := by decide
def rev97_plane59 : IntegerPlane := ⟨(-699324000000),(-2145688000000),(-1149963272359)⟩
theorem rev97_plane59_mem : rev97_plane59 ∈ rev97_planes := by decide
def rev97_plane76 : IntegerPlane := ⟨287616000000,(-1855520000000),(-211760240400)⟩
theorem rev97_plane76_mem : rev97_plane76 ∈ rev97_planes := by decide
def rev97_vertex0 : FractionPoint := fractionRow97[0]!
theorem rev97_vertex0_mem : rev97_vertex0∈fractionRow97 := by decide
def rev97_vertex1 : FractionPoint := fractionRow97[1]!
theorem rev97_vertex1_mem : rev97_vertex1∈fractionRow97 := by decide
def rev97_vertex2 : FractionPoint := fractionRow97[2]!
theorem rev97_vertex2_mem : rev97_vertex2∈fractionRow97 := by decide
def rev97_s0_ll : FractionPoint := ⟨20118659135039889,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev97_s0_ll_mem : rev97_s0_ll.real ∈ rationalHull (fractionRow97.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow97 rev97_plane59 rev97_vertex1 rev97_vertex2 rev97_s0_ll
    rev97_vertex1_mem rev97_vertex2_mem (by decide)
def rev97_s0_lr : FractionPoint := ⟨10496302777651103,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev97_s0_lr_mem : rev97_s0_lr.real ∈ rationalHull (fractionRow97.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow97 rev97_plane59 rev97_vertex1 rev97_vertex2 rev97_s0_lr
    rev97_vertex1_mem rev97_vertex2_mem (by decide)
def rev97_s0_ul : FractionPoint := ⟨20118659135039889,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev97_s0_ul_mem : rev97_s0_ul.real ∈ rationalHull (fractionRow97.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow97 rev97_plane28 rev97_vertex1 rev97_vertex0 rev97_s0_ul
    rev97_vertex1_mem rev97_vertex0_mem (by decide)
def rev97_s0_ur : FractionPoint := ⟨10496302777651103,11967149176800000,2846341088442900910319,10669132341338388000000⟩
theorem rev97_s0_ur_mem : rev97_s0_ur.real ∈ rationalHull (fractionRow97.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow97 rev97_plane28 rev97_vertex1 rev97_vertex0 rev97_s0_ur
    rev97_vertex1_mem rev97_vertex0_mem (by decide)
theorem rev97_slab0 (p : Point) (hp : p∈IntegerCarrier rev97_planes)
    (hx0 : rev97_s0_ll.real.1≤p.1) (hx1 : p.1≤rev97_s0_lr.real.1) :
    p∈rationalHull (fractionRow97.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev97_plane59 rev97_plane28 rev97_s0_ll rev97_s0_lr rev97_s0_ul rev97_s0_ur
    (by decide) rev97_s0_ll_mem rev97_s0_lr_mem rev97_s0_ul_mem rev97_s0_ur_mem p
    (hp _ rev97_plane59_mem) (hp _ rev97_plane28_mem) hx0 hx1
def rev97_s1_ll : FractionPoint := ⟨10496302777651103,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev97_s1_ll_mem : rev97_s1_ll.real ∈ rationalHull (fractionRow97.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow97 rev97_plane76 rev97_vertex2 rev97_vertex0 rev97_s1_ll
    rev97_vertex2_mem rev97_vertex0_mem (by decide)
def rev97_s1_lr : FractionPoint := ⟨657116793708449,670436124400000,127407110603973,478882946000000⟩
theorem rev97_s1_lr_mem : rev97_s1_lr.real ∈ rationalHull (fractionRow97.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow97 rev97_plane76 rev97_vertex2 rev97_vertex0 rev97_s1_lr
    rev97_vertex2_mem rev97_vertex0_mem (by decide)
def rev97_s1_ul : FractionPoint := ⟨10496302777651103,11967149176800000,2846341088442900910319,10669132341338388000000⟩
theorem rev97_s1_ul_mem : rev97_s1_ul.real ∈ rationalHull (fractionRow97.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow97 rev97_plane28 rev97_vertex1 rev97_vertex0 rev97_s1_ul
    rev97_vertex1_mem rev97_vertex0_mem (by decide)
def rev97_s1_ur : FractionPoint := ⟨657116793708449,670436124400000,127407110603973,478882946000000⟩
theorem rev97_s1_ur_mem : rev97_s1_ur.real ∈ rationalHull (fractionRow97.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow97 rev97_plane28 rev97_vertex1 rev97_vertex0 rev97_s1_ur
    rev97_vertex1_mem rev97_vertex0_mem (by decide)
theorem rev97_slab1 (p : Point) (hp : p∈IntegerCarrier rev97_planes)
    (hx0 : rev97_s1_ll.real.1≤p.1) (hx1 : p.1≤rev97_s1_lr.real.1) :
    p∈rationalHull (fractionRow97.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev97_plane76 rev97_plane28 rev97_s1_ll rev97_s1_lr rev97_s1_ul rev97_s1_ur
    (by decide) rev97_s1_ll_mem rev97_s1_lr_mem rev97_s1_ul_mem rev97_s1_ur_mem p
    (hp _ rev97_plane76_mem) (hp _ rev97_plane28_mem) hx0 hx1
theorem rev97_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev97_planes) : rev97_s0_ll.real.1≤p.1 := by
  have hc := rev97_plane28.combine_sound rev97_plane59 2145688000000 2139684000000 (by decide) (by decide) p
    (hp _ rev97_plane28_mem) (hp _ rev97_plane59_mem)
  exact (rev97_plane28.combine rev97_plane59 2145688000000 2139684000000).xBoundCheck_sound rev97_s0_ll.nx rev97_s0_ll.dx true (by decide) p hc
theorem rev97_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev97_planes) : p.1≤rev97_s1_lr.real.1 := by
  have hc := rev97_plane28.combine_sound rev97_plane76 1855520000000 2139684000000 (by decide) (by decide) p
    (hp _ rev97_plane28_mem) (hp _ rev97_plane76_mem)
  exact (rev97_plane28.combine rev97_plane76 1855520000000 2139684000000).xBoundCheck_sound rev97_s1_lr.nx rev97_s1_lr.dx false (by decide) p hc
theorem rev97_hull (p : Point) (hp : p∈IntegerCarrier rev97_planes) :
    p∈rationalHull (fractionRow97.map FractionPoint.rational) := by
  have hxlo := rev97_bound0_lo p hp
  have hxhi := rev97_bound0_hi p hp
  by_cases h0 : p.1≤rev97_s0_lr.real.1
  · exact rev97_slab0 p hp hxlo h0
  exact rev97_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull97 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,0,14,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow97 := by
  rw [← fractionRow97_correct]
  exact rev97_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull97
