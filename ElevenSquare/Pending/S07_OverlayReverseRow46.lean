import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks5
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev46_planes : List IntegerPlane := integerOverlayPlanes ![4,7,3,1]
def rev46_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev46_plane0_mem : rev46_plane0 ∈ rev46_planes := by decide
def rev46_plane4 : IntegerPlane := ⟨15204000000,(-2139684000000),(-568962228432)⟩
theorem rev46_plane4_mem : rev46_plane4 ∈ rev46_planes := by decide
def rev46_plane46 : IntegerPlane := ⟨287616000000,1855520000000,499376240400⟩
theorem rev46_plane46_mem : rev46_plane46 ∈ rev46_planes := by decide
def rev46_vertex0 : FractionPoint := fractionRow46[0]!
theorem rev46_vertex0_mem : rev46_vertex0∈fractionRow46 := by decide
def rev46_vertex1 : FractionPoint := fractionRow46[1]!
theorem rev46_vertex1_mem : rev46_vertex1∈fractionRow46 := by decide
def rev46_vertex2 : FractionPoint := fractionRow46[2]!
theorem rev46_vertex2_mem : rev46_vertex2∈fractionRow46 := by decide
def rev46_s0_ll : FractionPoint := ⟨0,1,11853379759,44576750000⟩
theorem rev46_s0_ll_mem : rev46_s0_ll.real ∈ rationalHull (fractionRow46.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow46 rev46_plane4 rev46_vertex1 rev46_vertex2 rev46_s0_ll
    rev46_vertex1_mem rev46_vertex2_mem (by decide)
def rev46_s0_lr : FractionPoint := ⟨13319330691551,670436124400000,127407110603973,478882946000000⟩
theorem rev46_s0_lr_mem : rev46_s0_lr.real ∈ rationalHull (fractionRow46.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow46 rev46_plane4 rev46_vertex1 rev46_vertex2 rev46_s0_lr
    rev46_vertex1_mem rev46_vertex2_mem (by decide)
def rev46_s0_ul : FractionPoint := ⟨0,1,1248440601,4638800000⟩
theorem rev46_s0_ul_mem : rev46_s0_ul.real ∈ rationalHull (fractionRow46.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow46 rev46_plane46 rev46_vertex0 rev46_vertex2 rev46_s0_ul
    rev46_vertex0_mem rev46_vertex2_mem (by decide)
def rev46_s0_ur : FractionPoint := ⟨13319330691551,670436124400000,127407110603973,478882946000000⟩
theorem rev46_s0_ur_mem : rev46_s0_ur.real ∈ rationalHull (fractionRow46.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow46 rev46_plane46 rev46_vertex0 rev46_vertex2 rev46_s0_ur
    rev46_vertex0_mem rev46_vertex2_mem (by decide)
theorem rev46_slab0 (p : Point) (hp : p∈IntegerCarrier rev46_planes)
    (hx0 : rev46_s0_ll.real.1≤p.1) (hx1 : p.1≤rev46_s0_lr.real.1) :
    p∈rationalHull (fractionRow46.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev46_plane4 rev46_plane46 rev46_s0_ll rev46_s0_lr rev46_s0_ul rev46_s0_ur
    (by decide) rev46_s0_ll_mem rev46_s0_lr_mem rev46_s0_ul_mem rev46_s0_ur_mem p
    (hp _ rev46_plane4_mem) (hp _ rev46_plane46_mem) hx0 hx1
theorem rev46_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev46_planes) : rev46_s0_ll.real.1≤p.1 := by
  have hc := rev46_plane0.combine_sound rev46_plane0 1 0 (by decide) (by decide) p
    (hp _ rev46_plane0_mem) (hp _ rev46_plane0_mem)
  exact (rev46_plane0.combine rev46_plane0 1 0).xBoundCheck_sound rev46_s0_ll.nx rev46_s0_ll.dx true (by decide) p hc
theorem rev46_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev46_planes) : p.1≤rev46_s0_lr.real.1 := by
  have hc := rev46_plane4.combine_sound rev46_plane46 1855520000000 2139684000000 (by decide) (by decide) p
    (hp _ rev46_plane4_mem) (hp _ rev46_plane46_mem)
  exact (rev46_plane4.combine rev46_plane46 1855520000000 2139684000000).xBoundCheck_sound rev46_s0_lr.nx rev46_s0_lr.dx false (by decide) p hc
theorem rev46_hull (p : Point) (hp : p∈IntegerCarrier rev46_planes) :
    p∈rationalHull (fractionRow46.map FractionPoint.rational) := by
  have hxlo := rev46_bound0_lo p hp
  have hxhi := rev46_bound0_hi p hp
  exact rev46_slab0 p hp hxlo hxhi
theorem overlay_in_hull46 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,7,3,1] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow46 := by
  rw [← fractionRow46_correct]
  exact rev46_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull46
