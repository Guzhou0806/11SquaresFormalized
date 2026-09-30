import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks14
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev115_planes : List IntegerPlane := integerOverlayPlanes ![8,11,1,1]
def rev115_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev115_plane0_mem : rev115_plane0 ∈ rev115_planes := by decide
def rev115_plane8 : IntegerPlane := ⟨(-48252000000),(-2112760000000),(-1130009250915)⟩
theorem rev115_plane8_mem : rev115_plane8 ∈ rev115_planes := by decide
def rev115_plane66 : IntegerPlane := ⟨746024000000,2083356000000,1117516707941⟩
theorem rev115_plane66_mem : rev115_plane66 ∈ rev115_planes := by decide
def rev115_vertex0 : FractionPoint := fractionRow115[0]!
theorem rev115_vertex0_mem : rev115_vertex0∈fractionRow115 := by decide
def rev115_vertex1 : FractionPoint := fractionRow115[1]!
theorem rev115_vertex1_mem : rev115_vertex1∈fractionRow115 := by decide
def rev115_vertex2 : FractionPoint := fractionRow115[2]!
theorem rev115_vertex2_mem : rev115_vertex2∈fractionRow115 := by decide
def rev115_s0_ll : FractionPoint := ⟨0,1,226001850183,422552000000⟩
theorem rev115_s0_ll_mem : rev115_s0_ll.real ∈ rationalHull (fractionRow115.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow115 rev115_plane8 rev115_vertex1 rev115_vertex2 rev115_s0_ll
    rev115_vertex1_mem rev115_vertex2_mem (by decide)
def rev115_s0_lr : FractionPoint := ⟨341652346007821,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev115_s0_lr_mem : rev115_s0_lr.real ∈ rationalHull (fractionRow115.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow115 rev115_plane8 rev115_vertex1 rev115_vertex2 rev115_s0_lr
    rev115_vertex1_mem rev115_vertex2_mem (by decide)
def rev115_s0_ul : FractionPoint := ⟨0,1,1117516707941,2083356000000⟩
theorem rev115_s0_ul_mem : rev115_s0_ul.real ∈ rationalHull (fractionRow115.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow115 rev115_plane66 rev115_vertex0 rev115_vertex2 rev115_s0_ul
    rev115_vertex0_mem rev115_vertex2_mem (by decide)
def rev115_s0_ur : FractionPoint := ⟨341652346007821,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev115_s0_ur_mem : rev115_s0_ur.real ∈ rationalHull (fractionRow115.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow115 rev115_plane66 rev115_vertex0 rev115_vertex2 rev115_s0_ur
    rev115_vertex0_mem rev115_vertex2_mem (by decide)
theorem rev115_slab0 (p : Point) (hp : p∈IntegerCarrier rev115_planes)
    (hx0 : rev115_s0_ll.real.1≤p.1) (hx1 : p.1≤rev115_s0_lr.real.1) :
    p∈rationalHull (fractionRow115.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev115_plane8 rev115_plane66 rev115_s0_ll rev115_s0_lr rev115_s0_ul rev115_s0_ur
    (by decide) rev115_s0_ll_mem rev115_s0_lr_mem rev115_s0_ul_mem rev115_s0_ur_mem p
    (hp _ rev115_plane8_mem) (hp _ rev115_plane66_mem) hx0 hx1
theorem rev115_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev115_planes) : rev115_s0_ll.real.1≤p.1 := by
  have hc := rev115_plane0.combine_sound rev115_plane0 1 0 (by decide) (by decide) p
    (hp _ rev115_plane0_mem) (hp _ rev115_plane0_mem)
  exact (rev115_plane0.combine rev115_plane0 1 0).xBoundCheck_sound rev115_s0_ll.nx rev115_s0_ll.dx true (by decide) p hc
theorem rev115_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev115_planes) : p.1≤rev115_s0_lr.real.1 := by
  have hc := rev115_plane8.combine_sound rev115_plane66 2083356000000 2112760000000 (by decide) (by decide) p
    (hp _ rev115_plane8_mem) (hp _ rev115_plane66_mem)
  exact (rev115_plane8.combine rev115_plane66 2083356000000 2112760000000).xBoundCheck_sound rev115_s0_lr.nx rev115_s0_lr.dx false (by decide) p hc
theorem rev115_hull (p : Point) (hp : p∈IntegerCarrier rev115_planes) :
    p∈rationalHull (fractionRow115.map FractionPoint.rational) := by
  have hxlo := rev115_bound0_lo p hp
  have hxhi := rev115_bound0_hi p hp
  exact rev115_slab0 p hp hxlo hxhi
theorem overlay_in_hull115 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,11,1,1] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow115 := by
  rw [← fractionRow115_correct]
  exact rev115_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull115
