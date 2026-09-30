import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks12
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev96_planes : List IntegerPlane := integerOverlayPlanes ![7,0,14,12]
def rev96_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev96_plane1_mem : rev96_plane1 ∈ rev96_planes := by decide
def rev96_plane28 : IntegerPlane := ⟨15204000000,2139684000000,584166228432⟩
theorem rev96_plane28_mem : rev96_plane28 ∈ rev96_planes := by decide
def rev96_plane59 : IntegerPlane := ⟨(-699324000000),(-2145688000000),(-1149963272359)⟩
theorem rev96_plane59_mem : rev96_plane59 ∈ rev96_planes := by decide
def rev96_plane77 : IntegerPlane := ⟨(-287616000000),1855520000000,211760240400⟩
theorem rev96_plane77_mem : rev96_plane77 ∈ rev96_planes := by decide
def rev96_vertex0 : FractionPoint := fractionRow96[0]!
theorem rev96_vertex0_mem : rev96_vertex0∈fractionRow96 := by decide
def rev96_vertex1 : FractionPoint := fractionRow96[1]!
theorem rev96_vertex1_mem : rev96_vertex1∈fractionRow96 := by decide
def rev96_vertex2 : FractionPoint := fractionRow96[2]!
theorem rev96_vertex2_mem : rev96_vertex2∈fractionRow96 := by decide
def rev96_vertex3 : FractionPoint := fractionRow96[3]!
theorem rev96_vertex3_mem : rev96_vertex3∈fractionRow96 := by decide
def rev96_s0_ll : FractionPoint := ⟨10496302777651103,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev96_s0_ll_mem : rev96_s0_ll.real ∈ rationalHull (fractionRow96.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow96 rev96_plane59 rev96_vertex3 rev96_vertex0 rev96_s0_ll
    rev96_vertex3_mem rev96_vertex0_mem (by decide)
def rev96_s0_lr : FractionPoint := ⟨657116793708449,670436124400000,778598437198355542459,3596366867228968000000⟩
theorem rev96_s0_lr_mem : rev96_s0_lr.real ∈ rationalHull (fractionRow96.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow96 rev96_plane59 rev96_vertex3 rev96_vertex0 rev96_s0_lr
    rev96_vertex3_mem rev96_vertex0_mem (by decide)
def rev96_s0_ul : FractionPoint := ⟨10496302777651103,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev96_s0_ul_mem : rev96_s0_ul.real ∈ rationalHull (fractionRow96.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow96 rev96_plane77 rev96_vertex3 rev96_vertex2 rev96_s0_ul
    rev96_vertex3_mem rev96_vertex2_mem (by decide)
def rev96_s0_ur : FractionPoint := ⟨657116793708449,670436124400000,127407110603973,478882946000000⟩
theorem rev96_s0_ur_mem : rev96_s0_ur.real ∈ rationalHull (fractionRow96.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow96 rev96_plane77 rev96_vertex3 rev96_vertex2 rev96_s0_ur
    rev96_vertex3_mem rev96_vertex2_mem (by decide)
theorem rev96_slab0 (p : Point) (hp : p∈IntegerCarrier rev96_planes)
    (hx0 : rev96_s0_ll.real.1≤p.1) (hx1 : p.1≤rev96_s0_lr.real.1) :
    p∈rationalHull (fractionRow96.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev96_plane59 rev96_plane77 rev96_s0_ll rev96_s0_lr rev96_s0_ul rev96_s0_ur
    (by decide) rev96_s0_ll_mem rev96_s0_lr_mem rev96_s0_ul_mem rev96_s0_ur_mem p
    (hp _ rev96_plane59_mem) (hp _ rev96_plane77_mem) hx0 hx1
def rev96_s1_ll : FractionPoint := ⟨657116793708449,670436124400000,778598437198355542459,3596366867228968000000⟩
theorem rev96_s1_ll_mem : rev96_s1_ll.real ∈ rationalHull (fractionRow96.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow96 rev96_plane59 rev96_vertex3 rev96_vertex0 rev96_s1_ll
    rev96_vertex3_mem rev96_vertex0_mem (by decide)
def rev96_s1_lr : FractionPoint := ⟨1,1,450639272359,2145688000000⟩
theorem rev96_s1_lr_mem : rev96_s1_lr.real ∈ rationalHull (fractionRow96.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow96 rev96_plane59 rev96_vertex3 rev96_vertex0 rev96_s1_lr
    rev96_vertex3_mem rev96_vertex0_mem (by decide)
def rev96_s1_ul : FractionPoint := ⟨657116793708449,670436124400000,127407110603973,478882946000000⟩
theorem rev96_s1_ul_mem : rev96_s1_ul.real ∈ rationalHull (fractionRow96.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow96 rev96_plane28 rev96_vertex2 rev96_vertex1 rev96_s1_ul
    rev96_vertex2_mem rev96_vertex1_mem (by decide)
def rev96_s1_ur : FractionPoint := ⟨1,1,11853379759,44576750000⟩
theorem rev96_s1_ur_mem : rev96_s1_ur.real ∈ rationalHull (fractionRow96.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow96 rev96_plane28 rev96_vertex2 rev96_vertex1 rev96_s1_ur
    rev96_vertex2_mem rev96_vertex1_mem (by decide)
theorem rev96_slab1 (p : Point) (hp : p∈IntegerCarrier rev96_planes)
    (hx0 : rev96_s1_ll.real.1≤p.1) (hx1 : p.1≤rev96_s1_lr.real.1) :
    p∈rationalHull (fractionRow96.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev96_plane59 rev96_plane28 rev96_s1_ll rev96_s1_lr rev96_s1_ul rev96_s1_ur
    (by decide) rev96_s1_ll_mem rev96_s1_lr_mem rev96_s1_ul_mem rev96_s1_ur_mem p
    (hp _ rev96_plane59_mem) (hp _ rev96_plane28_mem) hx0 hx1
theorem rev96_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev96_planes) : rev96_s0_ll.real.1≤p.1 := by
  have hc := rev96_plane59.combine_sound rev96_plane77 1855520000000 2145688000000 (by decide) (by decide) p
    (hp _ rev96_plane59_mem) (hp _ rev96_plane77_mem)
  exact (rev96_plane59.combine rev96_plane77 1855520000000 2145688000000).xBoundCheck_sound rev96_s0_ll.nx rev96_s0_ll.dx true (by decide) p hc
theorem rev96_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev96_planes) : p.1≤rev96_s1_lr.real.1 := by
  have hc := rev96_plane1.combine_sound rev96_plane1 1 0 (by decide) (by decide) p
    (hp _ rev96_plane1_mem) (hp _ rev96_plane1_mem)
  exact (rev96_plane1.combine rev96_plane1 1 0).xBoundCheck_sound rev96_s1_lr.nx rev96_s1_lr.dx false (by decide) p hc
theorem rev96_hull (p : Point) (hp : p∈IntegerCarrier rev96_planes) :
    p∈rationalHull (fractionRow96.map FractionPoint.rational) := by
  have hxlo := rev96_bound0_lo p hp
  have hxhi := rev96_bound0_hi p hp
  by_cases h0 : p.1≤rev96_s0_lr.real.1
  · exact rev96_slab0 p hp hxlo h0
  exact rev96_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull96 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,0,14,12] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow96 := by
  rw [← fractionRow96_correct]
  exact rev96_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull96
