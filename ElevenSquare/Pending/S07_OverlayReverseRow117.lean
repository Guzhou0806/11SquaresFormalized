import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks14
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev117_planes : List IntegerPlane := integerOverlayPlanes ![8,11,1,3]
def rev117_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev117_plane0_mem : rev117_plane0 ∈ rev117_planes := by decide
def rev117_plane39 : IntegerPlane := ⟨15204000000,2139684000000,1570721771568⟩
theorem rev117_plane39_mem : rev117_plane39 ∈ rev117_planes := by decide
def rev117_plane66 : IntegerPlane := ⟨287616000000,(-1855520000000),(-1356143759600)⟩
theorem rev117_plane66_mem : rev117_plane66 ∈ rev117_planes := by decide
def rev117_vertex0 : FractionPoint := fractionRow117[0]!
theorem rev117_vertex0_mem : rev117_vertex0∈fractionRow117 := by decide
def rev117_vertex1 : FractionPoint := fractionRow117[1]!
theorem rev117_vertex1_mem : rev117_vertex1∈fractionRow117 := by decide
def rev117_vertex2 : FractionPoint := fractionRow117[2]!
theorem rev117_vertex2_mem : rev117_vertex2∈fractionRow117 := by decide
def rev117_s0_ll : FractionPoint := ⟨0,1,3390359399,4638800000⟩
theorem rev117_s0_ll_mem : rev117_s0_ll.real ∈ rationalHull (fractionRow117.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow117 rev117_plane66 rev117_vertex1 rev117_vertex2 rev117_s0_ll
    rev117_vertex1_mem rev117_vertex2_mem (by decide)
def rev117_s0_lr : FractionPoint := ⟨13319330691551,670436124400000,351475835396027,478882946000000⟩
theorem rev117_s0_lr_mem : rev117_s0_lr.real ∈ rationalHull (fractionRow117.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow117 rev117_plane66 rev117_vertex1 rev117_vertex2 rev117_s0_lr
    rev117_vertex1_mem rev117_vertex2_mem (by decide)
def rev117_s0_ul : FractionPoint := ⟨0,1,32723370241,44576750000⟩
theorem rev117_s0_ul_mem : rev117_s0_ul.real ∈ rationalHull (fractionRow117.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow117 rev117_plane39 rev117_vertex0 rev117_vertex2 rev117_s0_ul
    rev117_vertex0_mem rev117_vertex2_mem (by decide)
def rev117_s0_ur : FractionPoint := ⟨13319330691551,670436124400000,351475835396027,478882946000000⟩
theorem rev117_s0_ur_mem : rev117_s0_ur.real ∈ rationalHull (fractionRow117.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow117 rev117_plane39 rev117_vertex0 rev117_vertex2 rev117_s0_ur
    rev117_vertex0_mem rev117_vertex2_mem (by decide)
theorem rev117_slab0 (p : Point) (hp : p∈IntegerCarrier rev117_planes)
    (hx0 : rev117_s0_ll.real.1≤p.1) (hx1 : p.1≤rev117_s0_lr.real.1) :
    p∈rationalHull (fractionRow117.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev117_plane66 rev117_plane39 rev117_s0_ll rev117_s0_lr rev117_s0_ul rev117_s0_ur
    (by decide) rev117_s0_ll_mem rev117_s0_lr_mem rev117_s0_ul_mem rev117_s0_ur_mem p
    (hp _ rev117_plane66_mem) (hp _ rev117_plane39_mem) hx0 hx1
theorem rev117_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev117_planes) : rev117_s0_ll.real.1≤p.1 := by
  have hc := rev117_plane0.combine_sound rev117_plane0 1 0 (by decide) (by decide) p
    (hp _ rev117_plane0_mem) (hp _ rev117_plane0_mem)
  exact (rev117_plane0.combine rev117_plane0 1 0).xBoundCheck_sound rev117_s0_ll.nx rev117_s0_ll.dx true (by decide) p hc
theorem rev117_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev117_planes) : p.1≤rev117_s0_lr.real.1 := by
  have hc := rev117_plane39.combine_sound rev117_plane66 1855520000000 2139684000000 (by decide) (by decide) p
    (hp _ rev117_plane39_mem) (hp _ rev117_plane66_mem)
  exact (rev117_plane39.combine rev117_plane66 1855520000000 2139684000000).xBoundCheck_sound rev117_s0_lr.nx rev117_s0_lr.dx false (by decide) p hc
theorem rev117_hull (p : Point) (hp : p∈IntegerCarrier rev117_planes) :
    p∈rationalHull (fractionRow117.map FractionPoint.rational) := by
  have hxlo := rev117_bound0_lo p hp
  have hxhi := rev117_bound0_hi p hp
  exact rev117_slab0 p hp hxlo hxhi
theorem overlay_in_hull117 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,11,1,3] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow117 := by
  rw [← fractionRow117_correct]
  exact rev117_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull117
