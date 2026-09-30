import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks2
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev20_planes : List IntegerPlane := integerOverlayPlanes ![2,0,11,8]
def rev20_plane25 : IntegerPlane := ⟨(-2145688000000),(-699324000000),(-1695048727641)⟩
theorem rev20_plane25_mem : rev20_plane25 ∈ rev20_planes := by decide
def rev20_plane29 : IntegerPlane := ⟨(-2129316000000),1440116000000,(-1301343880216)⟩
theorem rev20_plane29_mem : rev20_plane29 ∈ rev20_planes := by decide
def rev20_plane59 : IntegerPlane := ⟨2139684000000,15204000000,1570721771568⟩
theorem rev20_plane59_mem : rev20_plane59 ∈ rev20_planes := by decide
def rev20_vertex0 : FractionPoint := fractionRow20[0]!
theorem rev20_vertex0_mem : rev20_vertex0∈fractionRow20 := by decide
def rev20_vertex1 : FractionPoint := fractionRow20[1]!
theorem rev20_vertex1_mem : rev20_vertex1∈fractionRow20 := by decide
def rev20_vertex2 : FractionPoint := fractionRow20[2]!
theorem rev20_vertex2_mem : rev20_vertex2∈fractionRow20 := by decide
def rev20_s0_ll : FractionPoint := ⟨167556390057181017,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev20_s0_ll_mem : rev20_s0_ll.real ∈ rationalHull (fractionRow20.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow20 rev20_plane25 rev20_vertex1 rev20_vertex2 rev20_s0_ll
    rev20_vertex1_mem rev20_vertex2_mem (by decide)
def rev20_s0_lr : FractionPoint := ⟨23768824866023187,32435075873000000,1326183933446795745979,7560875666603284000000⟩
theorem rev20_s0_lr_mem : rev20_s0_lr.real ∈ rationalHull (fractionRow20.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow20 rev20_plane25 rev20_vertex1 rev20_vertex2 rev20_s0_lr
    rev20_vertex1_mem rev20_vertex2_mem (by decide)
def rev20_s0_ul : FractionPoint := ⟨167556390057181017,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev20_s0_ul_mem : rev20_s0_ul.real ∈ rationalHull (fractionRow20.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow20 rev20_plane29 rev20_vertex1 rev20_vertex0 rev20_s0_ul
    rev20_vertex1_mem rev20_vertex0_mem (by decide)
def rev20_s0_ur : FractionPoint := ⟨23768824866023187,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev20_s0_ur_mem : rev20_s0_ur.real ∈ rationalHull (fractionRow20.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow20 rev20_plane29 rev20_vertex1 rev20_vertex0 rev20_s0_ur
    rev20_vertex1_mem rev20_vertex0_mem (by decide)
theorem rev20_slab0 (p : Point) (hp : p∈IntegerCarrier rev20_planes)
    (hx0 : rev20_s0_ll.real.1≤p.1) (hx1 : p.1≤rev20_s0_lr.real.1) :
    p∈rationalHull (fractionRow20.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev20_plane25 rev20_plane29 rev20_s0_ll rev20_s0_lr rev20_s0_ul rev20_s0_ur
    (by decide) rev20_s0_ll_mem rev20_s0_lr_mem rev20_s0_ul_mem rev20_s0_ur_mem p
    (hp _ rev20_plane25_mem) (hp _ rev20_plane29_mem) hx0 hx1
def rev20_s1_ll : FractionPoint := ⟨23768824866023187,32435075873000000,1326183933446795745979,7560875666603284000000⟩
theorem rev20_s1_ll_mem : rev20_s1_ll.real ∈ rationalHull (fractionRow20.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow20 rev20_plane25 rev20_vertex1 rev20_vertex2 rev20_s1_ll
    rev20_vertex1_mem rev20_vertex2_mem (by decide)
def rev20_s1_lr : FractionPoint := ⟨89389325943747189,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev20_s1_lr_mem : rev20_s1_lr.real ∈ rationalHull (fractionRow20.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow20 rev20_plane25 rev20_vertex1 rev20_vertex2 rev20_s1_lr
    rev20_vertex1_mem rev20_vertex2_mem (by decide)
def rev20_s1_ul : FractionPoint := ⟨23768824866023187,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev20_s1_ul_mem : rev20_s1_ul.real ∈ rationalHull (fractionRow20.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow20 rev20_plane59 rev20_vertex0 rev20_vertex2 rev20_s1_ul
    rev20_vertex0_mem rev20_vertex2_mem (by decide)
def rev20_s1_ur : FractionPoint := ⟨89389325943747189,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev20_s1_ur_mem : rev20_s1_ur.real ∈ rationalHull (fractionRow20.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow20 rev20_plane59 rev20_vertex0 rev20_vertex2 rev20_s1_ur
    rev20_vertex0_mem rev20_vertex2_mem (by decide)
theorem rev20_slab1 (p : Point) (hp : p∈IntegerCarrier rev20_planes)
    (hx0 : rev20_s1_ll.real.1≤p.1) (hx1 : p.1≤rev20_s1_lr.real.1) :
    p∈rationalHull (fractionRow20.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev20_plane25 rev20_plane59 rev20_s1_ll rev20_s1_lr rev20_s1_ul rev20_s1_ur
    (by decide) rev20_s1_ll_mem rev20_s1_lr_mem rev20_s1_ul_mem rev20_s1_ur_mem p
    (hp _ rev20_plane25_mem) (hp _ rev20_plane59_mem) hx0 hx1
theorem rev20_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev20_planes) : rev20_s0_ll.real.1≤p.1 := by
  have hc := rev20_plane25.combine_sound rev20_plane29 1440116000000 699324000000 (by decide) (by decide) p
    (hp _ rev20_plane25_mem) (hp _ rev20_plane29_mem)
  exact (rev20_plane25.combine rev20_plane29 1440116000000 699324000000).xBoundCheck_sound rev20_s0_ll.nx rev20_s0_ll.dx true (by decide) p hc
theorem rev20_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev20_planes) : p.1≤rev20_s1_lr.real.1 := by
  have hc := rev20_plane25.combine_sound rev20_plane59 15204000000 699324000000 (by decide) (by decide) p
    (hp _ rev20_plane25_mem) (hp _ rev20_plane59_mem)
  exact (rev20_plane25.combine rev20_plane59 15204000000 699324000000).xBoundCheck_sound rev20_s1_lr.nx rev20_s1_lr.dx false (by decide) p hc
theorem rev20_hull (p : Point) (hp : p∈IntegerCarrier rev20_planes) :
    p∈rationalHull (fractionRow20.map FractionPoint.rational) := by
  have hxlo := rev20_bound0_lo p hp
  have hxhi := rev20_bound0_hi p hp
  by_cases h0 : p.1≤rev20_s0_lr.real.1
  · exact rev20_slab0 p hp hxlo h0
  exact rev20_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull20 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,0,11,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow20 := by
  rw [← fractionRow20_correct]
  exact rev20_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull20
