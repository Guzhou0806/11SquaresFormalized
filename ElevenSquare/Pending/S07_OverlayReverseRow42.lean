import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks5
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev42_planes : List IntegerPlane := integerOverlayPlanes ![4,7,1,1]
def rev42_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev42_plane0_mem : rev42_plane0 ∈ rev42_planes := by decide
def rev42_plane35 : IntegerPlane := ⟨(-48252000000),2112760000000,982750749085⟩
theorem rev42_plane35_mem : rev42_plane35 ∈ rev42_planes := by decide
def rev42_plane46 : IntegerPlane := ⟨746024000000,(-2083356000000),(-965839292059)⟩
theorem rev42_plane46_mem : rev42_plane46 ∈ rev42_planes := by decide
def rev42_vertex0 : FractionPoint := fractionRow42[0]!
theorem rev42_vertex0_mem : rev42_vertex0∈fractionRow42 := by decide
def rev42_vertex1 : FractionPoint := fractionRow42[1]!
theorem rev42_vertex1_mem : rev42_vertex1∈fractionRow42 := by decide
def rev42_vertex2 : FractionPoint := fractionRow42[2]!
theorem rev42_vertex2_mem : rev42_vertex2∈fractionRow42 := by decide
def rev42_s0_ll : FractionPoint := ⟨0,1,965839292059,2083356000000⟩
theorem rev42_s0_ll_mem : rev42_s0_ll.real ∈ rationalHull (fractionRow42.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow42 rev42_plane46 rev42_vertex1 rev42_vertex2 rev42_s0_ll
    rev42_vertex1_mem rev42_vertex2_mem (by decide)
def rev42_s0_lr : FractionPoint := ⟨341652346007821,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev42_s0_lr_mem : rev42_s0_lr.real ∈ rationalHull (fractionRow42.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow42 rev42_plane46 rev42_vertex1 rev42_vertex2 rev42_s0_lr
    rev42_vertex1_mem rev42_vertex2_mem (by decide)
def rev42_s0_ul : FractionPoint := ⟨0,1,196550149817,422552000000⟩
theorem rev42_s0_ul_mem : rev42_s0_ul.real ∈ rationalHull (fractionRow42.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow42 rev42_plane35 rev42_vertex0 rev42_vertex2 rev42_s0_ul
    rev42_vertex0_mem rev42_vertex2_mem (by decide)
def rev42_s0_ur : FractionPoint := ⟨341652346007821,73782178626400000,171637991828739293,368910893132000000⟩
theorem rev42_s0_ur_mem : rev42_s0_ur.real ∈ rationalHull (fractionRow42.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow42 rev42_plane35 rev42_vertex0 rev42_vertex2 rev42_s0_ur
    rev42_vertex0_mem rev42_vertex2_mem (by decide)
theorem rev42_slab0 (p : Point) (hp : p∈IntegerCarrier rev42_planes)
    (hx0 : rev42_s0_ll.real.1≤p.1) (hx1 : p.1≤rev42_s0_lr.real.1) :
    p∈rationalHull (fractionRow42.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev42_plane46 rev42_plane35 rev42_s0_ll rev42_s0_lr rev42_s0_ul rev42_s0_ur
    (by decide) rev42_s0_ll_mem rev42_s0_lr_mem rev42_s0_ul_mem rev42_s0_ur_mem p
    (hp _ rev42_plane46_mem) (hp _ rev42_plane35_mem) hx0 hx1
theorem rev42_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev42_planes) : rev42_s0_ll.real.1≤p.1 := by
  have hc := rev42_plane0.combine_sound rev42_plane0 1 0 (by decide) (by decide) p
    (hp _ rev42_plane0_mem) (hp _ rev42_plane0_mem)
  exact (rev42_plane0.combine rev42_plane0 1 0).xBoundCheck_sound rev42_s0_ll.nx rev42_s0_ll.dx true (by decide) p hc
theorem rev42_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev42_planes) : p.1≤rev42_s0_lr.real.1 := by
  have hc := rev42_plane35.combine_sound rev42_plane46 2083356000000 2112760000000 (by decide) (by decide) p
    (hp _ rev42_plane35_mem) (hp _ rev42_plane46_mem)
  exact (rev42_plane35.combine rev42_plane46 2083356000000 2112760000000).xBoundCheck_sound rev42_s0_lr.nx rev42_s0_lr.dx false (by decide) p hc
theorem rev42_hull (p : Point) (hp : p∈IntegerCarrier rev42_planes) :
    p∈rationalHull (fractionRow42.map FractionPoint.rational) := by
  have hxlo := rev42_bound0_lo p hp
  have hxhi := rev42_bound0_hi p hp
  exact rev42_slab0 p hp hxlo hxhi
theorem overlay_in_hull42 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,7,1,1] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow42 := by
  rw [← fractionRow42_correct]
  exact rev42_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull42
