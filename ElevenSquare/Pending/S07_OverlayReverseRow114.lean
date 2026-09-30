import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks14
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev114_planes : List IntegerPlane := integerOverlayPlanes ![8,11,0,2]
def rev114_plane39 : IntegerPlane := ⟨15204000000,2139684000000,1570721771568⟩
theorem rev114_plane39_mem : rev114_plane39 ∈ rev114_planes := by decide
def rev114_plane45 : IntegerPlane := ⟨(-699324000000),(-2145688000000),(-1695048727641)⟩
theorem rev114_plane45_mem : rev114_plane45 ∈ rev114_planes := by decide
def rev114_plane49 : IntegerPlane := ⟨1440116000000,(-2129316000000),(-1301343880216)⟩
theorem rev114_plane49_mem : rev114_plane49 ∈ rev114_planes := by decide
def rev114_vertex0 : FractionPoint := fractionRow114[0]!
theorem rev114_vertex0_mem : rev114_vertex0∈fractionRow114 := by decide
def rev114_vertex1 : FractionPoint := fractionRow114[1]!
theorem rev114_vertex1_mem : rev114_vertex1∈fractionRow114 := by decide
def rev114_vertex2 : FractionPoint := fractionRow114[2]!
theorem rev114_vertex2_mem : rev114_vertex2∈fractionRow114 := by decide
def rev114_s0_ll : FractionPoint := ⟨4276496419360111,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev114_s0_ll_mem : rev114_s0_ll.real ∈ rationalHull (fractionRow114.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow114 rev114_plane45 rev114_vertex1 rev114_vertex2 rev114_s0_ll
    rev114_vertex1_mem rev114_vertex2_mem (by decide)
def rev114_s0_lr : FractionPoint := ⟨204254107223178737,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev114_s0_lr_mem : rev114_s0_lr.real ∈ rationalHull (fractionRow114.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow114 rev114_plane45 rev114_vertex1 rev114_vertex2 rev114_s0_lr
    rev114_vertex1_mem rev114_vertex2_mem (by decide)
def rev114_s0_ul : FractionPoint := ⟨4276496419360111,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev114_s0_ul_mem : rev114_s0_ul.real ∈ rationalHull (fractionRow114.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow114 rev114_plane39 rev114_vertex1 rev114_vertex0 rev114_s0_ul
    rev114_vertex1_mem rev114_vertex0_mem (by decide)
def rev114_s0_ur : FractionPoint := ⟨204254107223178737,1144780350548000000,149585495068564117508493,204122349965162236000000⟩
theorem rev114_s0_ur_mem : rev114_s0_ur.real ∈ rationalHull (fractionRow114.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow114 rev114_plane39 rev114_vertex1 rev114_vertex0 rev114_s0_ur
    rev114_vertex1_mem rev114_vertex0_mem (by decide)
theorem rev114_slab0 (p : Point) (hp : p∈IntegerCarrier rev114_planes)
    (hx0 : rev114_s0_ll.real.1≤p.1) (hx1 : p.1≤rev114_s0_lr.real.1) :
    p∈rationalHull (fractionRow114.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev114_plane45 rev114_plane39 rev114_s0_ll rev114_s0_lr rev114_s0_ul rev114_s0_ur
    (by decide) rev114_s0_ll_mem rev114_s0_lr_mem rev114_s0_ul_mem rev114_s0_ur_mem p
    (hp _ rev114_plane45_mem) (hp _ rev114_plane39_mem) hx0 hx1
def rev114_s1_ll : FractionPoint := ⟨204254107223178737,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev114_s1_ll_mem : rev114_s1_ll.real ∈ rationalHull (fractionRow114.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow114 rev114_plane49 rev114_vertex2 rev114_vertex0 rev114_s1_ll
    rev114_vertex2_mem rev114_vertex0_mem (by decide)
def rev114_s1_lr : FractionPoint := ⟨5834357507833289,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev114_s1_lr_mem : rev114_s1_lr.real ∈ rationalHull (fractionRow114.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow114 rev114_plane49 rev114_vertex2 rev114_vertex0 rev114_s1_lr
    rev114_vertex2_mem rev114_vertex0_mem (by decide)
def rev114_s1_ul : FractionPoint := ⟨204254107223178737,1144780350548000000,149585495068564117508493,204122349965162236000000⟩
theorem rev114_s1_ul_mem : rev114_s1_ul.real ∈ rationalHull (fractionRow114.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow114 rev114_plane39 rev114_vertex1 rev114_vertex0 rev114_s1_ul
    rev114_vertex1_mem rev114_vertex0_mem (by decide)
def rev114_s1_ur : FractionPoint := ⟨5834357507833289,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev114_s1_ur_mem : rev114_s1_ur.real ∈ rationalHull (fractionRow114.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow114 rev114_plane39 rev114_vertex1 rev114_vertex0 rev114_s1_ur
    rev114_vertex1_mem rev114_vertex0_mem (by decide)
theorem rev114_slab1 (p : Point) (hp : p∈IntegerCarrier rev114_planes)
    (hx0 : rev114_s1_ll.real.1≤p.1) (hx1 : p.1≤rev114_s1_lr.real.1) :
    p∈rationalHull (fractionRow114.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev114_plane49 rev114_plane39 rev114_s1_ll rev114_s1_lr rev114_s1_ul rev114_s1_ur
    (by decide) rev114_s1_ll_mem rev114_s1_lr_mem rev114_s1_ul_mem rev114_s1_ur_mem p
    (hp _ rev114_plane49_mem) (hp _ rev114_plane39_mem) hx0 hx1
theorem rev114_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev114_planes) : rev114_s0_ll.real.1≤p.1 := by
  have hc := rev114_plane39.combine_sound rev114_plane45 2145688000000 2139684000000 (by decide) (by decide) p
    (hp _ rev114_plane39_mem) (hp _ rev114_plane45_mem)
  exact (rev114_plane39.combine rev114_plane45 2145688000000 2139684000000).xBoundCheck_sound rev114_s0_ll.nx rev114_s0_ll.dx true (by decide) p hc
theorem rev114_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev114_planes) : p.1≤rev114_s1_lr.real.1 := by
  have hc := rev114_plane39.combine_sound rev114_plane49 2129316000000 2139684000000 (by decide) (by decide) p
    (hp _ rev114_plane39_mem) (hp _ rev114_plane49_mem)
  exact (rev114_plane39.combine rev114_plane49 2129316000000 2139684000000).xBoundCheck_sound rev114_s1_lr.nx rev114_s1_lr.dx false (by decide) p hc
theorem rev114_hull (p : Point) (hp : p∈IntegerCarrier rev114_planes) :
    p∈rationalHull (fractionRow114.map FractionPoint.rational) := by
  have hxlo := rev114_bound0_lo p hp
  have hxhi := rev114_bound0_hi p hp
  by_cases h0 : p.1≤rev114_s0_lr.real.1
  · exact rev114_slab0 p hp hxlo h0
  exact rev114_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull114 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,11,0,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow114 := by
  rw [← fractionRow114_correct]
  exact rev114_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull114
