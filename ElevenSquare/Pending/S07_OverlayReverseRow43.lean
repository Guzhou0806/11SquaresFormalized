import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks5
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev43_planes : List IntegerPlane := integerOverlayPlanes ![4,7,2,0]
def rev43_plane4 : IntegerPlane := ⟨15204000000,(-2139684000000),(-568962228432)⟩
theorem rev43_plane4_mem : rev43_plane4 ∈ rev43_planes := by decide
def rev43_plane65 : IntegerPlane := ⟨(-699324000000),2145688000000,450639272359⟩
theorem rev43_plane65_mem : rev43_plane65 ∈ rev43_planes := by decide
def rev43_plane69 : IntegerPlane := ⟨1440116000000,2129316000000,827972119784⟩
theorem rev43_plane69_mem : rev43_plane69 ∈ rev43_planes := by decide
def rev43_vertex0 : FractionPoint := fractionRow43[0]!
theorem rev43_vertex0_mem : rev43_vertex0∈fractionRow43 := by decide
def rev43_vertex1 : FractionPoint := fractionRow43[1]!
theorem rev43_vertex1_mem : rev43_vertex1∈fractionRow43 := by decide
def rev43_vertex2 : FractionPoint := fractionRow43[2]!
theorem rev43_vertex2_mem : rev43_vertex2∈fractionRow43 := by decide
def rev43_s0_ll : FractionPoint := ⟨4276496419360111,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev43_s0_ll_mem : rev43_s0_ll.real ∈ rationalHull (fractionRow43.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow43 rev43_plane4 rev43_vertex0 rev43_vertex1 rev43_s0_ll
    rev43_vertex0_mem rev43_vertex1_mem (by decide)
def rev43_s0_lr : FractionPoint := ⟨204254107223178737,1144780350548000000,54536854896598118491507,204122349965162236000000⟩
theorem rev43_s0_lr_mem : rev43_s0_lr.real ∈ rationalHull (fractionRow43.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow43 rev43_plane4 rev43_vertex0 rev43_vertex1 rev43_s0_lr
    rev43_vertex0_mem rev43_vertex1_mem (by decide)
def rev43_s0_ul : FractionPoint := ⟨4276496419360111,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev43_s0_ul_mem : rev43_s0_ul.real ∈ rationalHull (fractionRow43.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow43 rev43_plane65 rev43_vertex0 rev43_vertex2 rev43_s0_ul
    rev43_vertex0_mem rev43_vertex2_mem (by decide)
def rev43_s0_ur : FractionPoint := ⟨204254107223178737,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev43_s0_ur_mem : rev43_s0_ur.real ∈ rationalHull (fractionRow43.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow43 rev43_plane65 rev43_vertex0 rev43_vertex2 rev43_s0_ur
    rev43_vertex0_mem rev43_vertex2_mem (by decide)
theorem rev43_slab0 (p : Point) (hp : p∈IntegerCarrier rev43_planes)
    (hx0 : rev43_s0_ll.real.1≤p.1) (hx1 : p.1≤rev43_s0_lr.real.1) :
    p∈rationalHull (fractionRow43.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev43_plane4 rev43_plane65 rev43_s0_ll rev43_s0_lr rev43_s0_ul rev43_s0_ur
    (by decide) rev43_s0_ll_mem rev43_s0_lr_mem rev43_s0_ul_mem rev43_s0_ur_mem p
    (hp _ rev43_plane4_mem) (hp _ rev43_plane65_mem) hx0 hx1
def rev43_s1_ll : FractionPoint := ⟨204254107223178737,1144780350548000000,54536854896598118491507,204122349965162236000000⟩
theorem rev43_s1_ll_mem : rev43_s1_ll.real ∈ rationalHull (fractionRow43.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow43 rev43_plane4 rev43_vertex0 rev43_vertex1 rev43_s1_ll
    rev43_vertex0_mem rev43_vertex1_mem (by decide)
def rev43_s1_lr : FractionPoint := ⟨5834357507833289,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev43_s1_lr_mem : rev43_s1_lr.real ∈ rationalHull (fractionRow43.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow43 rev43_plane4 rev43_vertex0 rev43_vertex1 rev43_s1_lr
    rev43_vertex0_mem rev43_vertex1_mem (by decide)
def rev43_s1_ul : FractionPoint := ⟨204254107223178737,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev43_s1_ul_mem : rev43_s1_ul.real ∈ rationalHull (fractionRow43.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow43 rev43_plane69 rev43_vertex2 rev43_vertex1 rev43_s1_ul
    rev43_vertex2_mem rev43_vertex1_mem (by decide)
def rev43_s1_ur : FractionPoint := ⟨5834357507833289,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev43_s1_ur_mem : rev43_s1_ur.real ∈ rationalHull (fractionRow43.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow43 rev43_plane69 rev43_vertex2 rev43_vertex1 rev43_s1_ur
    rev43_vertex2_mem rev43_vertex1_mem (by decide)
theorem rev43_slab1 (p : Point) (hp : p∈IntegerCarrier rev43_planes)
    (hx0 : rev43_s1_ll.real.1≤p.1) (hx1 : p.1≤rev43_s1_lr.real.1) :
    p∈rationalHull (fractionRow43.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev43_plane4 rev43_plane69 rev43_s1_ll rev43_s1_lr rev43_s1_ul rev43_s1_ur
    (by decide) rev43_s1_ll_mem rev43_s1_lr_mem rev43_s1_ul_mem rev43_s1_ur_mem p
    (hp _ rev43_plane4_mem) (hp _ rev43_plane69_mem) hx0 hx1
theorem rev43_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev43_planes) : rev43_s0_ll.real.1≤p.1 := by
  have hc := rev43_plane4.combine_sound rev43_plane65 2145688000000 2139684000000 (by decide) (by decide) p
    (hp _ rev43_plane4_mem) (hp _ rev43_plane65_mem)
  exact (rev43_plane4.combine rev43_plane65 2145688000000 2139684000000).xBoundCheck_sound rev43_s0_ll.nx rev43_s0_ll.dx true (by decide) p hc
theorem rev43_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev43_planes) : p.1≤rev43_s1_lr.real.1 := by
  have hc := rev43_plane4.combine_sound rev43_plane69 2129316000000 2139684000000 (by decide) (by decide) p
    (hp _ rev43_plane4_mem) (hp _ rev43_plane69_mem)
  exact (rev43_plane4.combine rev43_plane69 2129316000000 2139684000000).xBoundCheck_sound rev43_s1_lr.nx rev43_s1_lr.dx false (by decide) p hc
theorem rev43_hull (p : Point) (hp : p∈IntegerCarrier rev43_planes) :
    p∈rationalHull (fractionRow43.map FractionPoint.rational) := by
  have hxlo := rev43_bound0_lo p hp
  have hxhi := rev43_bound0_hi p hp
  by_cases h0 : p.1≤rev43_s0_lr.real.1
  · exact rev43_slab0 p hp hxlo h0
  exact rev43_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull43 (p : Point)
    (hp : ∀ g, ClosedCell ((![4,7,2,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow43 := by
  rw [← fractionRow43_correct]
  exact rev43_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull43
