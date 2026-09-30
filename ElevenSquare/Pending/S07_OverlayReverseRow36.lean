import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks4
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev36_planes : List IntegerPlane := integerOverlayPlanes ![3,1,11,8]
def rev36_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev36_plane2_mem : rev36_plane2 ∈ rev36_planes := by decide
def rev36_plane6 : IntegerPlane := ⟨(-1855520000000),287616000000,(-1356143759600)⟩
theorem rev36_plane6_mem : rev36_plane6 ∈ rev36_planes := by decide
def rev36_plane59 : IntegerPlane := ⟨2139684000000,15204000000,1570721771568⟩
theorem rev36_plane59_mem : rev36_plane59 ∈ rev36_planes := by decide
def rev36_vertex0 : FractionPoint := fractionRow36[0]!
theorem rev36_vertex0_mem : rev36_vertex0∈fractionRow36 := by decide
def rev36_vertex1 : FractionPoint := fractionRow36[1]!
theorem rev36_vertex1_mem : rev36_vertex1∈fractionRow36 := by decide
def rev36_vertex2 : FractionPoint := fractionRow36[2]!
theorem rev36_vertex2_mem : rev36_vertex2∈fractionRow36 := by decide
def rev36_s0_ll : FractionPoint := ⟨3390359399,4638800000,0,1⟩
theorem rev36_s0_ll_mem : rev36_s0_ll.real ∈ rationalHull (fractionRow36.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow36 rev36_plane2 rev36_vertex0 rev36_vertex1 rev36_s0_ll
    rev36_vertex0_mem rev36_vertex1_mem (by decide)
def rev36_s0_lr : FractionPoint := ⟨351475835396027,478882946000000,0,1⟩
theorem rev36_s0_lr_mem : rev36_s0_lr.real ∈ rationalHull (fractionRow36.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow36 rev36_plane2 rev36_vertex0 rev36_vertex1 rev36_s0_lr
    rev36_vertex0_mem rev36_vertex1_mem (by decide)
def rev36_s0_ul : FractionPoint := ⟨3390359399,4638800000,0,1⟩
theorem rev36_s0_ul_mem : rev36_s0_ul.real ∈ rationalHull (fractionRow36.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow36 rev36_plane6 rev36_vertex0 rev36_vertex2 rev36_s0_ul
    rev36_vertex0_mem rev36_vertex2_mem (by decide)
def rev36_s0_ur : FractionPoint := ⟨351475835396027,478882946000000,13319330691551,670436124400000⟩
theorem rev36_s0_ur_mem : rev36_s0_ur.real ∈ rationalHull (fractionRow36.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow36 rev36_plane6 rev36_vertex0 rev36_vertex2 rev36_s0_ur
    rev36_vertex0_mem rev36_vertex2_mem (by decide)
theorem rev36_slab0 (p : Point) (hp : p∈IntegerCarrier rev36_planes)
    (hx0 : rev36_s0_ll.real.1≤p.1) (hx1 : p.1≤rev36_s0_lr.real.1) :
    p∈rationalHull (fractionRow36.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev36_plane2 rev36_plane6 rev36_s0_ll rev36_s0_lr rev36_s0_ul rev36_s0_ur
    (by decide) rev36_s0_ll_mem rev36_s0_lr_mem rev36_s0_ul_mem rev36_s0_ur_mem p
    (hp _ rev36_plane2_mem) (hp _ rev36_plane6_mem) hx0 hx1
def rev36_s1_ll : FractionPoint := ⟨351475835396027,478882946000000,0,1⟩
theorem rev36_s1_ll_mem : rev36_s1_ll.real ∈ rationalHull (fractionRow36.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow36 rev36_plane2 rev36_vertex0 rev36_vertex1 rev36_s1_ll
    rev36_vertex0_mem rev36_vertex1_mem (by decide)
def rev36_s1_lr : FractionPoint := ⟨32723370241,44576750000,0,1⟩
theorem rev36_s1_lr_mem : rev36_s1_lr.real ∈ rationalHull (fractionRow36.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow36 rev36_plane2 rev36_vertex0 rev36_vertex1 rev36_s1_lr
    rev36_vertex0_mem rev36_vertex1_mem (by decide)
def rev36_s1_ul : FractionPoint := ⟨351475835396027,478882946000000,13319330691551,670436124400000⟩
theorem rev36_s1_ul_mem : rev36_s1_ul.real ∈ rationalHull (fractionRow36.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow36 rev36_plane59 rev36_vertex2 rev36_vertex1 rev36_s1_ul
    rev36_vertex2_mem rev36_vertex1_mem (by decide)
def rev36_s1_ur : FractionPoint := ⟨32723370241,44576750000,0,1⟩
theorem rev36_s1_ur_mem : rev36_s1_ur.real ∈ rationalHull (fractionRow36.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow36 rev36_plane59 rev36_vertex2 rev36_vertex1 rev36_s1_ur
    rev36_vertex2_mem rev36_vertex1_mem (by decide)
theorem rev36_slab1 (p : Point) (hp : p∈IntegerCarrier rev36_planes)
    (hx0 : rev36_s1_ll.real.1≤p.1) (hx1 : p.1≤rev36_s1_lr.real.1) :
    p∈rationalHull (fractionRow36.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev36_plane2 rev36_plane59 rev36_s1_ll rev36_s1_lr rev36_s1_ul rev36_s1_ur
    (by decide) rev36_s1_ll_mem rev36_s1_lr_mem rev36_s1_ul_mem rev36_s1_ur_mem p
    (hp _ rev36_plane2_mem) (hp _ rev36_plane59_mem) hx0 hx1
theorem rev36_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev36_planes) : rev36_s0_ll.real.1≤p.1 := by
  have hc := rev36_plane2.combine_sound rev36_plane6 287616000000 1 (by decide) (by decide) p
    (hp _ rev36_plane2_mem) (hp _ rev36_plane6_mem)
  exact (rev36_plane2.combine rev36_plane6 287616000000 1).xBoundCheck_sound rev36_s0_ll.nx rev36_s0_ll.dx true (by decide) p hc
theorem rev36_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev36_planes) : p.1≤rev36_s1_lr.real.1 := by
  have hc := rev36_plane2.combine_sound rev36_plane59 15204000000 1 (by decide) (by decide) p
    (hp _ rev36_plane2_mem) (hp _ rev36_plane59_mem)
  exact (rev36_plane2.combine rev36_plane59 15204000000 1).xBoundCheck_sound rev36_s1_lr.nx rev36_s1_lr.dx false (by decide) p hc
theorem rev36_hull (p : Point) (hp : p∈IntegerCarrier rev36_planes) :
    p∈rationalHull (fractionRow36.map FractionPoint.rational) := by
  have hxlo := rev36_bound0_lo p hp
  have hxhi := rev36_bound0_hi p hp
  by_cases h0 : p.1≤rev36_s0_lr.real.1
  · exact rev36_slab0 p hp hxlo h0
  exact rev36_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull36 (p : Point)
    (hp : ∀ g, ClosedCell ((![3,1,11,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow36 := by
  rw [← fractionRow36_correct]
  exact rev36_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull36
