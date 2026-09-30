import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks0
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev1_planes : List IntegerPlane := integerOverlayPlanes ![0,2,7,4]
def rev1_plane5 : IntegerPlane := ⟨2145688000000,(-699324000000),450639272359⟩
theorem rev1_plane5_mem : rev1_plane5 ∈ rev1_planes := by decide
def rev1_plane9 : IntegerPlane := ⟨2129316000000,1440116000000,827972119784⟩
theorem rev1_plane9_mem : rev1_plane9 ∈ rev1_planes := by decide
def rev1_plane64 : IntegerPlane := ⟨(-2139684000000),15204000000,(-568962228432)⟩
theorem rev1_plane64_mem : rev1_plane64 ∈ rev1_planes := by decide
def rev1_vertex0 : FractionPoint := fractionRow1[0]!
theorem rev1_vertex0_mem : rev1_vertex0∈fractionRow1 := by decide
def rev1_vertex1 : FractionPoint := fractionRow1[1]!
theorem rev1_vertex1_mem : rev1_vertex1∈fractionRow1 := by decide
def rev1_vertex2 : FractionPoint := fractionRow1[2]!
theorem rev1_vertex2_mem : rev1_vertex2∈fractionRow1 := by decide
def rev1_s0_ll : FractionPoint := ⟨32586451828252811,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev1_s0_ll_mem : rev1_s0_ll.real ∈ rationalHull (fractionRow1.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow1 rev1_plane5 rev1_vertex0 rev1_vertex1 rev1_s0_ll
    rev1_vertex0_mem rev1_vertex1_mem (by decide)
def rev1_s0_lr : FractionPoint := ⟨8666251006976813,32435075873000000,1326183933446795745979,7560875666603284000000⟩
theorem rev1_s0_lr_mem : rev1_s0_lr.real ∈ rationalHull (fractionRow1.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow1 rev1_plane5 rev1_vertex0 rev1_vertex1 rev1_s0_lr
    rev1_vertex0_mem rev1_vertex1_mem (by decide)
def rev1_s0_ul : FractionPoint := ⟨32586451828252811,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev1_s0_ul_mem : rev1_s0_ul.real ∈ rationalHull (fractionRow1.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow1 rev1_plane64 rev1_vertex0 rev1_vertex2 rev1_s0_ul
    rev1_vertex0_mem rev1_vertex2_mem (by decide)
def rev1_s0_ur : FractionPoint := ⟨8666251006976813,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev1_s0_ur_mem : rev1_s0_ur.real ∈ rationalHull (fractionRow1.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow1 rev1_plane64 rev1_vertex0 rev1_vertex2 rev1_s0_ur
    rev1_vertex0_mem rev1_vertex2_mem (by decide)
theorem rev1_slab0 (p : Point) (hp : p∈IntegerCarrier rev1_planes)
    (hx0 : rev1_s0_ll.real.1≤p.1) (hx1 : p.1≤rev1_s0_lr.real.1) :
    p∈rationalHull (fractionRow1.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev1_plane5 rev1_plane64 rev1_s0_ll rev1_s0_lr rev1_s0_ul rev1_s0_ur
    (by decide) rev1_s0_ll_mem rev1_s0_lr_mem rev1_s0_ul_mem rev1_s0_ur_mem p
    (hp _ rev1_plane5_mem) (hp _ rev1_plane64_mem) hx0 hx1
def rev1_s1_ll : FractionPoint := ⟨8666251006976813,32435075873000000,1326183933446795745979,7560875666603284000000⟩
theorem rev1_s1_ll_mem : rev1_s1_ll.real ∈ rationalHull (fractionRow1.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow1 rev1_plane5 rev1_vertex0 rev1_vertex1 rev1_s1_ll
    rev1_vertex0_mem rev1_vertex1_mem (by decide)
def rev1_s1_lr : FractionPoint := ⟨61399680052418983,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev1_s1_lr_mem : rev1_s1_lr.real ∈ rationalHull (fractionRow1.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow1 rev1_plane5 rev1_vertex0 rev1_vertex1 rev1_s1_lr
    rev1_vertex0_mem rev1_vertex1_mem (by decide)
def rev1_s1_ul : FractionPoint := ⟨8666251006976813,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev1_s1_ul_mem : rev1_s1_ul.real ∈ rationalHull (fractionRow1.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow1 rev1_plane9 rev1_vertex2 rev1_vertex1 rev1_s1_ul
    rev1_vertex2_mem rev1_vertex1_mem (by decide)
def rev1_s1_ur : FractionPoint := ⟨61399680052418983,228956070109600000,204254107223178737,1144780350548000000⟩
theorem rev1_s1_ur_mem : rev1_s1_ur.real ∈ rationalHull (fractionRow1.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow1 rev1_plane9 rev1_vertex2 rev1_vertex1 rev1_s1_ur
    rev1_vertex2_mem rev1_vertex1_mem (by decide)
theorem rev1_slab1 (p : Point) (hp : p∈IntegerCarrier rev1_planes)
    (hx0 : rev1_s1_ll.real.1≤p.1) (hx1 : p.1≤rev1_s1_lr.real.1) :
    p∈rationalHull (fractionRow1.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev1_plane5 rev1_plane9 rev1_s1_ll rev1_s1_lr rev1_s1_ul rev1_s1_ur
    (by decide) rev1_s1_ll_mem rev1_s1_lr_mem rev1_s1_ul_mem rev1_s1_ur_mem p
    (hp _ rev1_plane5_mem) (hp _ rev1_plane9_mem) hx0 hx1
theorem rev1_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev1_planes) : rev1_s0_ll.real.1≤p.1 := by
  have hc := rev1_plane5.combine_sound rev1_plane64 15204000000 699324000000 (by decide) (by decide) p
    (hp _ rev1_plane5_mem) (hp _ rev1_plane64_mem)
  exact (rev1_plane5.combine rev1_plane64 15204000000 699324000000).xBoundCheck_sound rev1_s0_ll.nx rev1_s0_ll.dx true (by decide) p hc
theorem rev1_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev1_planes) : p.1≤rev1_s1_lr.real.1 := by
  have hc := rev1_plane5.combine_sound rev1_plane9 1440116000000 699324000000 (by decide) (by decide) p
    (hp _ rev1_plane5_mem) (hp _ rev1_plane9_mem)
  exact (rev1_plane5.combine rev1_plane9 1440116000000 699324000000).xBoundCheck_sound rev1_s1_lr.nx rev1_s1_lr.dx false (by decide) p hc
theorem rev1_hull (p : Point) (hp : p∈IntegerCarrier rev1_planes) :
    p∈rationalHull (fractionRow1.map FractionPoint.rational) := by
  have hxlo := rev1_bound0_lo p hp
  have hxhi := rev1_bound0_hi p hp
  by_cases h0 : p.1≤rev1_s0_lr.real.1
  · exact rev1_slab0 p hp hxlo h0
  exact rev1_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull1 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,2,7,4] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow1 := by
  rw [← fractionRow1_correct]
  exact rev1_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull1
