import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks24
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev195_planes : List IntegerPlane := integerOverlayPlanes ![13,14,0,7]
def rev195_plane16 : IntegerPlane := ⟨(-1855520000000),287616000000,(-211760240400)⟩
theorem rev195_plane16_mem : rev195_plane16 ∈ rev195_planes := by decide
def rev195_plane39 : IntegerPlane := ⟨(-2145688000000),(-699324000000),(-1149963272359)⟩
theorem rev195_plane39_mem : rev195_plane39 ∈ rev195_planes := by decide
def rev195_plane48 : IntegerPlane := ⟨2139684000000,15204000000,584166228432⟩
theorem rev195_plane48_mem : rev195_plane48 ∈ rev195_planes := by decide
def rev195_vertex0 : FractionPoint := fractionRow195[0]!
theorem rev195_vertex0_mem : rev195_vertex0∈fractionRow195 := by decide
def rev195_vertex1 : FractionPoint := fractionRow195[1]!
theorem rev195_vertex1_mem : rev195_vertex1∈fractionRow195 := by decide
def rev195_vertex2 : FractionPoint := fractionRow195[2]!
theorem rev195_vertex2_mem : rev195_vertex2∈fractionRow195 := by decide
def rev195_s0_ll : FractionPoint := ⟨2493941952605707,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev195_s0_ll_mem : rev195_s0_ll.real ∈ rationalHull (fractionRow195.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow195 rev195_plane39 rev195_vertex1 rev195_vertex2 rev195_s0_ll
    rev195_vertex1_mem rev195_vertex2_mem (by decide)
def rev195_s0_lr : FractionPoint := ⟨127407110603973,478882946000000,27732189132146067119,33489433732850400000⟩
theorem rev195_s0_lr_mem : rev195_s0_lr.real ∈ rationalHull (fractionRow195.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow195 rev195_plane39 rev195_vertex1 rev195_vertex2 rev195_s0_lr
    rev195_vertex1_mem rev195_vertex2_mem (by decide)
def rev195_s0_ul : FractionPoint := ⟨2493941952605707,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev195_s0_ul_mem : rev195_s0_ul.real ∈ rationalHull (fractionRow195.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow195 rev195_plane16 rev195_vertex1 rev195_vertex0 rev195_s0_ul
    rev195_vertex1_mem rev195_vertex0_mem (by decide)
def rev195_s0_ur : FractionPoint := ⟨127407110603973,478882946000000,657116793708449,670436124400000⟩
theorem rev195_s0_ur_mem : rev195_s0_ur.real ∈ rationalHull (fractionRow195.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow195 rev195_plane16 rev195_vertex1 rev195_vertex0 rev195_s0_ur
    rev195_vertex1_mem rev195_vertex0_mem (by decide)
theorem rev195_slab0 (p : Point) (hp : p∈IntegerCarrier rev195_planes)
    (hx0 : rev195_s0_ll.real.1≤p.1) (hx1 : p.1≤rev195_s0_lr.real.1) :
    p∈rationalHull (fractionRow195.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev195_plane39 rev195_plane16 rev195_s0_ll rev195_s0_lr rev195_s0_ul rev195_s0_ur
    (by decide) rev195_s0_ll_mem rev195_s0_lr_mem rev195_s0_ul_mem rev195_s0_ur_mem p
    (hp _ rev195_plane39_mem) (hp _ rev195_plane16_mem) hx0 hx1
def rev195_s1_ll : FractionPoint := ⟨127407110603973,478882946000000,27732189132146067119,33489433732850400000⟩
theorem rev195_s1_ll_mem : rev195_s1_ll.real ∈ rationalHull (fractionRow195.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow195 rev195_plane39 rev195_vertex1 rev195_vertex2 rev195_s1_ll
    rev195_vertex1_mem rev195_vertex2_mem (by decide)
def rev195_s1_lr : FractionPoint := ⟨32586451828252811,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev195_s1_lr_mem : rev195_s1_lr.real ∈ rationalHull (fractionRow195.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow195 rev195_plane39 rev195_vertex1 rev195_vertex2 rev195_s1_lr
    rev195_vertex1_mem rev195_vertex2_mem (by decide)
def rev195_s1_ul : FractionPoint := ⟨127407110603973,478882946000000,657116793708449,670436124400000⟩
theorem rev195_s1_ul_mem : rev195_s1_ul.real ∈ rationalHull (fractionRow195.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow195 rev195_plane48 rev195_vertex0 rev195_vertex2 rev195_s1_ul
    rev195_vertex0_mem rev195_vertex2_mem (by decide)
def rev195_s1_ur : FractionPoint := ⟨32586451828252811,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev195_s1_ur_mem : rev195_s1_ur.real ∈ rationalHull (fractionRow195.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow195 rev195_plane48 rev195_vertex0 rev195_vertex2 rev195_s1_ur
    rev195_vertex0_mem rev195_vertex2_mem (by decide)
theorem rev195_slab1 (p : Point) (hp : p∈IntegerCarrier rev195_planes)
    (hx0 : rev195_s1_ll.real.1≤p.1) (hx1 : p.1≤rev195_s1_lr.real.1) :
    p∈rationalHull (fractionRow195.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev195_plane39 rev195_plane48 rev195_s1_ll rev195_s1_lr rev195_s1_ul rev195_s1_ur
    (by decide) rev195_s1_ll_mem rev195_s1_lr_mem rev195_s1_ul_mem rev195_s1_ur_mem p
    (hp _ rev195_plane39_mem) (hp _ rev195_plane48_mem) hx0 hx1
theorem rev195_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev195_planes) : rev195_s0_ll.real.1≤p.1 := by
  have hc := rev195_plane16.combine_sound rev195_plane39 699324000000 287616000000 (by decide) (by decide) p
    (hp _ rev195_plane16_mem) (hp _ rev195_plane39_mem)
  exact (rev195_plane16.combine rev195_plane39 699324000000 287616000000).xBoundCheck_sound rev195_s0_ll.nx rev195_s0_ll.dx true (by decide) p hc
theorem rev195_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev195_planes) : p.1≤rev195_s1_lr.real.1 := by
  have hc := rev195_plane39.combine_sound rev195_plane48 15204000000 699324000000 (by decide) (by decide) p
    (hp _ rev195_plane39_mem) (hp _ rev195_plane48_mem)
  exact (rev195_plane39.combine rev195_plane48 15204000000 699324000000).xBoundCheck_sound rev195_s1_lr.nx rev195_s1_lr.dx false (by decide) p hc
theorem rev195_hull (p : Point) (hp : p∈IntegerCarrier rev195_planes) :
    p∈rationalHull (fractionRow195.map FractionPoint.rational) := by
  have hxlo := rev195_bound0_lo p hp
  have hxhi := rev195_bound0_hi p hp
  by_cases h0 : p.1≤rev195_s0_lr.real.1
  · exact rev195_slab0 p hp hxlo h0
  exact rev195_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull195 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,14,0,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow195 := by
  rw [← fractionRow195_correct]
  exact rev195_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull195
