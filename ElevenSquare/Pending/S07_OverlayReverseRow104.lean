import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks13
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev104_planes : List IntegerPlane := integerOverlayPlanes ![7,4,14,14]
def rev104_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev104_plane1_mem : rev104_plane1 ∈ rev104_planes := by decide
def rev104_plane15 : IntegerPlane := ⟨48252000000,2112760000000,1031002749085⟩
theorem rev104_plane15_mem : rev104_plane15 ∈ rev104_planes := by decide
def rev104_plane77 : IntegerPlane := ⟨(-746024000000),(-2083356000000),(-1711863292059)⟩
theorem rev104_plane77_mem : rev104_plane77 ∈ rev104_planes := by decide
def rev104_vertex0 : FractionPoint := fractionRow104[0]!
theorem rev104_vertex0_mem : rev104_vertex0∈fractionRow104 := by decide
def rev104_vertex1 : FractionPoint := fractionRow104[1]!
theorem rev104_vertex1_mem : rev104_vertex1∈fractionRow104 := by decide
def rev104_vertex2 : FractionPoint := fractionRow104[2]!
theorem rev104_vertex2_mem : rev104_vertex2∈fractionRow104 := by decide
def rev104_s0_ll : FractionPoint := ⟨73440526280392179,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev104_s0_ll_mem : rev104_s0_ll.real ∈ rationalHull (fractionRow104.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow104 rev104_plane77 rev104_vertex2 rev104_vertex0 rev104_s0_ll
    rev104_vertex2_mem rev104_vertex0_mem (by decide)
def rev104_s0_lr : FractionPoint := ⟨1,1,965839292059,2083356000000⟩
theorem rev104_s0_lr_mem : rev104_s0_lr.real ∈ rationalHull (fractionRow104.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow104 rev104_plane77 rev104_vertex2 rev104_vertex0 rev104_s0_lr
    rev104_vertex2_mem rev104_vertex0_mem (by decide)
def rev104_s0_ul : FractionPoint := ⟨73440526280392179,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev104_s0_ul_mem : rev104_s0_ul.real ∈ rationalHull (fractionRow104.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow104 rev104_plane15 rev104_vertex2 rev104_vertex1 rev104_s0_ul
    rev104_vertex2_mem rev104_vertex1_mem (by decide)
def rev104_s0_ur : FractionPoint := ⟨1,1,196550149817,422552000000⟩
theorem rev104_s0_ur_mem : rev104_s0_ur.real ∈ rationalHull (fractionRow104.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow104 rev104_plane15 rev104_vertex2 rev104_vertex1 rev104_s0_ur
    rev104_vertex2_mem rev104_vertex1_mem (by decide)
theorem rev104_slab0 (p : Point) (hp : p∈IntegerCarrier rev104_planes)
    (hx0 : rev104_s0_ll.real.1≤p.1) (hx1 : p.1≤rev104_s0_lr.real.1) :
    p∈rationalHull (fractionRow104.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev104_plane77 rev104_plane15 rev104_s0_ll rev104_s0_lr rev104_s0_ul rev104_s0_ur
    (by decide) rev104_s0_ll_mem rev104_s0_lr_mem rev104_s0_ul_mem rev104_s0_ur_mem p
    (hp _ rev104_plane77_mem) (hp _ rev104_plane15_mem) hx0 hx1
theorem rev104_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev104_planes) : rev104_s0_ll.real.1≤p.1 := by
  have hc := rev104_plane15.combine_sound rev104_plane77 2083356000000 2112760000000 (by decide) (by decide) p
    (hp _ rev104_plane15_mem) (hp _ rev104_plane77_mem)
  exact (rev104_plane15.combine rev104_plane77 2083356000000 2112760000000).xBoundCheck_sound rev104_s0_ll.nx rev104_s0_ll.dx true (by decide) p hc
theorem rev104_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev104_planes) : p.1≤rev104_s0_lr.real.1 := by
  have hc := rev104_plane1.combine_sound rev104_plane1 1 0 (by decide) (by decide) p
    (hp _ rev104_plane1_mem) (hp _ rev104_plane1_mem)
  exact (rev104_plane1.combine rev104_plane1 1 0).xBoundCheck_sound rev104_s0_lr.nx rev104_s0_lr.dx false (by decide) p hc
theorem rev104_hull (p : Point) (hp : p∈IntegerCarrier rev104_planes) :
    p∈rationalHull (fractionRow104.map FractionPoint.rational) := by
  have hxlo := rev104_bound0_lo p hp
  have hxhi := rev104_bound0_hi p hp
  exact rev104_slab0 p hp hxlo hxhi
theorem overlay_in_hull104 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,4,14,14] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow104 := by
  rw [← fractionRow104_correct]
  exact rev104_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull104
