import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks22
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev177_planes : List IntegerPlane := integerOverlayPlanes ![11,8,14,14]
def rev177_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev177_plane1_mem : rev177_plane1 ∈ rev177_planes := by decide
def rev177_plane28 : IntegerPlane := ⟨48252000000,(-2112760000000),(-1081757250915)⟩
theorem rev177_plane28_mem : rev177_plane28 ∈ rev177_planes := by decide
def rev177_plane57 : IntegerPlane := ⟨(-746024000000),2083356000000,371492707941⟩
theorem rev177_plane57_mem : rev177_plane57 ∈ rev177_planes := by decide
def rev177_vertex0 : FractionPoint := fractionRow177[0]!
theorem rev177_vertex0_mem : rev177_vertex0∈fractionRow177 := by decide
def rev177_vertex1 : FractionPoint := fractionRow177[1]!
theorem rev177_vertex1_mem : rev177_vertex1∈fractionRow177 := by decide
def rev177_vertex2 : FractionPoint := fractionRow177[2]!
theorem rev177_vertex2_mem : rev177_vertex2∈fractionRow177 := by decide
def rev177_s0_ll : FractionPoint := ⟨73440526280392179,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev177_s0_ll_mem : rev177_s0_ll.real ∈ rationalHull (fractionRow177.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow177 rev177_plane28 rev177_vertex2 rev177_vertex0 rev177_s0_ll
    rev177_vertex2_mem rev177_vertex0_mem (by decide)
def rev177_s0_lr : FractionPoint := ⟨1,1,226001850183,422552000000⟩
theorem rev177_s0_lr_mem : rev177_s0_lr.real ∈ rationalHull (fractionRow177.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow177 rev177_plane28 rev177_vertex2 rev177_vertex0 rev177_s0_lr
    rev177_vertex2_mem rev177_vertex0_mem (by decide)
def rev177_s0_ul : FractionPoint := ⟨73440526280392179,73782178626400000,197272901303260707,368910893132000000⟩
theorem rev177_s0_ul_mem : rev177_s0_ul.real ∈ rationalHull (fractionRow177.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow177 rev177_plane57 rev177_vertex2 rev177_vertex1 rev177_s0_ul
    rev177_vertex2_mem rev177_vertex1_mem (by decide)
def rev177_s0_ur : FractionPoint := ⟨1,1,1117516707941,2083356000000⟩
theorem rev177_s0_ur_mem : rev177_s0_ur.real ∈ rationalHull (fractionRow177.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow177 rev177_plane57 rev177_vertex2 rev177_vertex1 rev177_s0_ur
    rev177_vertex2_mem rev177_vertex1_mem (by decide)
theorem rev177_slab0 (p : Point) (hp : p∈IntegerCarrier rev177_planes)
    (hx0 : rev177_s0_ll.real.1≤p.1) (hx1 : p.1≤rev177_s0_lr.real.1) :
    p∈rationalHull (fractionRow177.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev177_plane28 rev177_plane57 rev177_s0_ll rev177_s0_lr rev177_s0_ul rev177_s0_ur
    (by decide) rev177_s0_ll_mem rev177_s0_lr_mem rev177_s0_ul_mem rev177_s0_ur_mem p
    (hp _ rev177_plane28_mem) (hp _ rev177_plane57_mem) hx0 hx1
theorem rev177_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev177_planes) : rev177_s0_ll.real.1≤p.1 := by
  have hc := rev177_plane28.combine_sound rev177_plane57 2083356000000 2112760000000 (by decide) (by decide) p
    (hp _ rev177_plane28_mem) (hp _ rev177_plane57_mem)
  exact (rev177_plane28.combine rev177_plane57 2083356000000 2112760000000).xBoundCheck_sound rev177_s0_ll.nx rev177_s0_ll.dx true (by decide) p hc
theorem rev177_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev177_planes) : p.1≤rev177_s0_lr.real.1 := by
  have hc := rev177_plane1.combine_sound rev177_plane1 1 0 (by decide) (by decide) p
    (hp _ rev177_plane1_mem) (hp _ rev177_plane1_mem)
  exact (rev177_plane1.combine rev177_plane1 1 0).xBoundCheck_sound rev177_s0_lr.nx rev177_s0_lr.dx false (by decide) p hc
theorem rev177_hull (p : Point) (hp : p∈IntegerCarrier rev177_planes) :
    p∈rationalHull (fractionRow177.map FractionPoint.rational) := by
  have hxlo := rev177_bound0_lo p hp
  have hxhi := rev177_bound0_hi p hp
  exact rev177_slab0 p hp hxlo hxhi
theorem overlay_in_hull177 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,8,14,14] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow177 := by
  rw [← fractionRow177_correct]
  exact rev177_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull177
