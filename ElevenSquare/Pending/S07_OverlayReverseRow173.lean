import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks21
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev173_planes : List IntegerPlane := integerOverlayPlanes ![11,8,12,14]
def rev173_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev173_plane1_mem : rev173_plane1 ∈ rev173_planes := by decide
def rev173_plane19 : IntegerPlane := ⟨(-15204000000),2139684000000,1555517771568⟩
theorem rev173_plane19_mem : rev173_plane19 ∈ rev173_planes := by decide
def rev173_plane57 : IntegerPlane := ⟨(-287616000000),(-1855520000000),(-1643759759600)⟩
theorem rev173_plane57_mem : rev173_plane57 ∈ rev173_planes := by decide
def rev173_vertex0 : FractionPoint := fractionRow173[0]!
theorem rev173_vertex0_mem : rev173_vertex0∈fractionRow173 := by decide
def rev173_vertex1 : FractionPoint := fractionRow173[1]!
theorem rev173_vertex1_mem : rev173_vertex1∈fractionRow173 := by decide
def rev173_vertex2 : FractionPoint := fractionRow173[2]!
theorem rev173_vertex2_mem : rev173_vertex2∈fractionRow173 := by decide
def rev173_s0_ll : FractionPoint := ⟨657116793708449,670436124400000,351475835396027,478882946000000⟩
theorem rev173_s0_ll_mem : rev173_s0_ll.real ∈ rationalHull (fractionRow173.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow173 rev173_plane57 rev173_vertex2 rev173_vertex0 rev173_s0_ll
    rev173_vertex2_mem rev173_vertex0_mem (by decide)
def rev173_s0_lr : FractionPoint := ⟨1,1,3390359399,4638800000⟩
theorem rev173_s0_lr_mem : rev173_s0_lr.real ∈ rationalHull (fractionRow173.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow173 rev173_plane57 rev173_vertex2 rev173_vertex0 rev173_s0_lr
    rev173_vertex2_mem rev173_vertex0_mem (by decide)
def rev173_s0_ul : FractionPoint := ⟨657116793708449,670436124400000,351475835396027,478882946000000⟩
theorem rev173_s0_ul_mem : rev173_s0_ul.real ∈ rationalHull (fractionRow173.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow173 rev173_plane19 rev173_vertex2 rev173_vertex1 rev173_s0_ul
    rev173_vertex2_mem rev173_vertex1_mem (by decide)
def rev173_s0_ur : FractionPoint := ⟨1,1,32723370241,44576750000⟩
theorem rev173_s0_ur_mem : rev173_s0_ur.real ∈ rationalHull (fractionRow173.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow173 rev173_plane19 rev173_vertex2 rev173_vertex1 rev173_s0_ur
    rev173_vertex2_mem rev173_vertex1_mem (by decide)
theorem rev173_slab0 (p : Point) (hp : p∈IntegerCarrier rev173_planes)
    (hx0 : rev173_s0_ll.real.1≤p.1) (hx1 : p.1≤rev173_s0_lr.real.1) :
    p∈rationalHull (fractionRow173.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev173_plane57 rev173_plane19 rev173_s0_ll rev173_s0_lr rev173_s0_ul rev173_s0_ur
    (by decide) rev173_s0_ll_mem rev173_s0_lr_mem rev173_s0_ul_mem rev173_s0_ur_mem p
    (hp _ rev173_plane57_mem) (hp _ rev173_plane19_mem) hx0 hx1
theorem rev173_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev173_planes) : rev173_s0_ll.real.1≤p.1 := by
  have hc := rev173_plane19.combine_sound rev173_plane57 1855520000000 2139684000000 (by decide) (by decide) p
    (hp _ rev173_plane19_mem) (hp _ rev173_plane57_mem)
  exact (rev173_plane19.combine rev173_plane57 1855520000000 2139684000000).xBoundCheck_sound rev173_s0_ll.nx rev173_s0_ll.dx true (by decide) p hc
theorem rev173_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev173_planes) : p.1≤rev173_s0_lr.real.1 := by
  have hc := rev173_plane1.combine_sound rev173_plane1 1 0 (by decide) (by decide) p
    (hp _ rev173_plane1_mem) (hp _ rev173_plane1_mem)
  exact (rev173_plane1.combine rev173_plane1 1 0).xBoundCheck_sound rev173_s0_lr.nx rev173_s0_lr.dx false (by decide) p hc
theorem rev173_hull (p : Point) (hp : p∈IntegerCarrier rev173_planes) :
    p∈rationalHull (fractionRow173.map FractionPoint.rational) := by
  have hxlo := rev173_bound0_lo p hp
  have hxhi := rev173_bound0_hi p hp
  exact rev173_slab0 p hp hxlo hxhi
theorem overlay_in_hull173 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,8,12,14] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow173 := by
  rw [← fractionRow173_correct]
  exact rev173_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull173
