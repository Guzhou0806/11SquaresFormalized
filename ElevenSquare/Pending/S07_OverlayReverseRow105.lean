import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks13
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev105_planes : List IntegerPlane := integerOverlayPlanes ![7,4,15,13]
def rev105_plane24 : IntegerPlane := ⟨(-15204000000),(-2139684000000),(-584166228432)⟩
theorem rev105_plane24_mem : rev105_plane24 ∈ rev105_planes := by decide
def rev105_plane54 : IntegerPlane := ⟨(-1440116000000),2129316000000,(-612143880216)⟩
theorem rev105_plane54_mem : rev105_plane54 ∈ rev105_planes := by decide
def rev105_plane58 : IntegerPlane := ⟨699324000000,2145688000000,1149963272359⟩
theorem rev105_plane58_mem : rev105_plane58 ∈ rev105_planes := by decide
def rev105_vertex0 : FractionPoint := fractionRow105[0]!
theorem rev105_vertex0_mem : rev105_vertex0∈fractionRow105 := by decide
def rev105_vertex1 : FractionPoint := fractionRow105[1]!
theorem rev105_vertex1_mem : rev105_vertex1∈fractionRow105 := by decide
def rev105_vertex2 : FractionPoint := fractionRow105[2]!
theorem rev105_vertex2_mem : rev105_vertex2∈fractionRow105 := by decide
def rev105_s0_ll : FractionPoint := ⟨26600718365166711,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev105_s0_ll_mem : rev105_s0_ll.real ∈ rationalHull (fractionRow105.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow105 rev105_plane24 rev105_vertex0 rev105_vertex1 rev105_s0_ll
    rev105_vertex0_mem rev105_vertex1_mem (by decide)
def rev105_s0_lr : FractionPoint := ⟨940526243324821263,1144780350548000000,54536854896598118491507,204122349965162236000000⟩
theorem rev105_s0_lr_mem : rev105_s0_lr.real ∈ rationalHull (fractionRow105.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow105 rev105_plane24 rev105_vertex0 rev105_vertex1 rev105_s0_lr
    rev105_vertex0_mem rev105_vertex1_mem (by decide)
def rev105_s0_ul : FractionPoint := ⟨26600718365166711,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev105_s0_ul_mem : rev105_s0_ul.real ∈ rationalHull (fractionRow105.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow105 rev105_plane54 rev105_vertex0 rev105_vertex2 rev105_s0_ul
    rev105_vertex0_mem rev105_vertex2_mem (by decide)
def rev105_s0_ur : FractionPoint := ⟨940526243324821263,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev105_s0_ur_mem : rev105_s0_ur.real ∈ rationalHull (fractionRow105.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow105 rev105_plane54 rev105_vertex0 rev105_vertex2 rev105_s0_ur
    rev105_vertex0_mem rev105_vertex2_mem (by decide)
theorem rev105_slab0 (p : Point) (hp : p∈IntegerCarrier rev105_planes)
    (hx0 : rev105_s0_ll.real.1≤p.1) (hx1 : p.1≤rev105_s0_lr.real.1) :
    p∈rationalHull (fractionRow105.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev105_plane24 rev105_plane54 rev105_s0_ll rev105_s0_lr rev105_s0_ul rev105_s0_ur
    (by decide) rev105_s0_ll_mem rev105_s0_lr_mem rev105_s0_ul_mem rev105_s0_ur_mem p
    (hp _ rev105_plane24_mem) (hp _ rev105_plane54_mem) hx0 hx1
def rev105_s1_ll : FractionPoint := ⟨940526243324821263,1144780350548000000,54536854896598118491507,204122349965162236000000⟩
theorem rev105_s1_ll_mem : rev105_s1_ll.real ∈ rationalHull (fractionRow105.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow105 rev105_plane24 rev105_vertex0 rev105_vertex1 rev105_s1_ll
    rev105_vertex0_mem rev105_vertex1_mem (by decide)
def rev105_s1_lr : FractionPoint := ⟨20118659135039889,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev105_s1_lr_mem : rev105_s1_lr.real ∈ rationalHull (fractionRow105.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow105 rev105_plane24 rev105_vertex0 rev105_vertex1 rev105_s1_lr
    rev105_vertex0_mem rev105_vertex1_mem (by decide)
def rev105_s1_ul : FractionPoint := ⟨940526243324821263,1144780350548000000,61399680052418983,228956070109600000⟩
theorem rev105_s1_ul_mem : rev105_s1_ul.real ∈ rationalHull (fractionRow105.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow105 rev105_plane58 rev105_vertex2 rev105_vertex1 rev105_s1_ul
    rev105_vertex2_mem rev105_vertex1_mem (by decide)
def rev105_s1_ur : FractionPoint := ⟨20118659135039889,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev105_s1_ur_mem : rev105_s1_ur.real ∈ rationalHull (fractionRow105.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow105 rev105_plane58 rev105_vertex2 rev105_vertex1 rev105_s1_ur
    rev105_vertex2_mem rev105_vertex1_mem (by decide)
theorem rev105_slab1 (p : Point) (hp : p∈IntegerCarrier rev105_planes)
    (hx0 : rev105_s1_ll.real.1≤p.1) (hx1 : p.1≤rev105_s1_lr.real.1) :
    p∈rationalHull (fractionRow105.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev105_plane24 rev105_plane58 rev105_s1_ll rev105_s1_lr rev105_s1_ul rev105_s1_ur
    (by decide) rev105_s1_ll_mem rev105_s1_lr_mem rev105_s1_ul_mem rev105_s1_ur_mem p
    (hp _ rev105_plane24_mem) (hp _ rev105_plane58_mem) hx0 hx1
theorem rev105_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev105_planes) : rev105_s0_ll.real.1≤p.1 := by
  have hc := rev105_plane24.combine_sound rev105_plane54 2129316000000 2139684000000 (by decide) (by decide) p
    (hp _ rev105_plane24_mem) (hp _ rev105_plane54_mem)
  exact (rev105_plane24.combine rev105_plane54 2129316000000 2139684000000).xBoundCheck_sound rev105_s0_ll.nx rev105_s0_ll.dx true (by decide) p hc
theorem rev105_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev105_planes) : p.1≤rev105_s1_lr.real.1 := by
  have hc := rev105_plane24.combine_sound rev105_plane58 2145688000000 2139684000000 (by decide) (by decide) p
    (hp _ rev105_plane24_mem) (hp _ rev105_plane58_mem)
  exact (rev105_plane24.combine rev105_plane58 2145688000000 2139684000000).xBoundCheck_sound rev105_s1_lr.nx rev105_s1_lr.dx false (by decide) p hc
theorem rev105_hull (p : Point) (hp : p∈IntegerCarrier rev105_planes) :
    p∈rationalHull (fractionRow105.map FractionPoint.rational) := by
  have hxlo := rev105_bound0_lo p hp
  have hxhi := rev105_bound0_hi p hp
  by_cases h0 : p.1≤rev105_s0_lr.real.1
  · exact rev105_slab0 p hp hxlo h0
  exact rev105_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull105 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,4,15,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow105 := by
  rw [← fractionRow105_correct]
  exact rev105_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull105
