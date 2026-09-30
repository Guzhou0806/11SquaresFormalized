import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks24
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev199_planes : List IntegerPlane := integerOverlayPlanes ![13,15,4,7]
def rev199_plane34 : IntegerPlane := ⟨2129316000000,(-1440116000000),(-612143880216)⟩
theorem rev199_plane34_mem : rev199_plane34 ∈ rev199_planes := by decide
def rev199_plane38 : IntegerPlane := ⟨2145688000000,699324000000,1149963272359⟩
theorem rev199_plane38_mem : rev199_plane38 ∈ rev199_planes := by decide
def rev199_plane44 : IntegerPlane := ⟨(-2139684000000),(-15204000000),(-584166228432)⟩
theorem rev199_plane44_mem : rev199_plane44 ∈ rev199_planes := by decide
def rev199_vertex0 : FractionPoint := fractionRow199[0]!
theorem rev199_vertex0_mem : rev199_vertex0∈fractionRow199 := by decide
def rev199_vertex1 : FractionPoint := fractionRow199[1]!
theorem rev199_vertex1_mem : rev199_vertex1∈fractionRow199 := by decide
def rev199_vertex2 : FractionPoint := fractionRow199[2]!
theorem rev199_vertex2_mem : rev199_vertex2∈fractionRow199 := by decide
def rev199_s0_ll : FractionPoint := ⟨32586451828252811,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev199_s0_ll_mem : rev199_s0_ll.real ∈ rationalHull (fractionRow199.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow199 rev199_plane44 rev199_vertex2 rev199_vertex0 rev199_s0_ll
    rev199_vertex2_mem rev199_vertex0_mem (by decide)
def rev199_s0_lr : FractionPoint := ⟨8666251006976813,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev199_s0_lr_mem : rev199_s0_lr.real ∈ rationalHull (fractionRow199.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow199 rev199_plane44 rev199_vertex2 rev199_vertex0 rev199_s0_lr
    rev199_vertex2_mem rev199_vertex0_mem (by decide)
def rev199_s0_ul : FractionPoint := ⟨32586451828252811,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev199_s0_ul_mem : rev199_s0_ul.real ∈ rationalHull (fractionRow199.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow199 rev199_plane38 rev199_vertex2 rev199_vertex1 rev199_s0_ul
    rev199_vertex2_mem rev199_vertex1_mem (by decide)
def rev199_s0_ur : FractionPoint := ⟨8666251006976813,32435075873000000,6234691733156488254021,7560875666603284000000⟩
theorem rev199_s0_ur_mem : rev199_s0_ur.real ∈ rationalHull (fractionRow199.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow199 rev199_plane38 rev199_vertex2 rev199_vertex1 rev199_s0_ur
    rev199_vertex2_mem rev199_vertex1_mem (by decide)
theorem rev199_slab0 (p : Point) (hp : p∈IntegerCarrier rev199_planes)
    (hx0 : rev199_s0_ll.real.1≤p.1) (hx1 : p.1≤rev199_s0_lr.real.1) :
    p∈rationalHull (fractionRow199.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev199_plane44 rev199_plane38 rev199_s0_ll rev199_s0_lr rev199_s0_ul rev199_s0_ur
    (by decide) rev199_s0_ll_mem rev199_s0_lr_mem rev199_s0_ul_mem rev199_s0_ur_mem p
    (hp _ rev199_plane44_mem) (hp _ rev199_plane38_mem) hx0 hx1
def rev199_s1_ll : FractionPoint := ⟨8666251006976813,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev199_s1_ll_mem : rev199_s1_ll.real ∈ rationalHull (fractionRow199.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow199 rev199_plane34 rev199_vertex0 rev199_vertex1 rev199_s1_ll
    rev199_vertex0_mem rev199_vertex1_mem (by decide)
def rev199_s1_lr : FractionPoint := ⟨61399680052418983,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev199_s1_lr_mem : rev199_s1_lr.real ∈ rationalHull (fractionRow199.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow199 rev199_plane34 rev199_vertex0 rev199_vertex1 rev199_s1_lr
    rev199_vertex0_mem rev199_vertex1_mem (by decide)
def rev199_s1_ul : FractionPoint := ⟨8666251006976813,32435075873000000,6234691733156488254021,7560875666603284000000⟩
theorem rev199_s1_ul_mem : rev199_s1_ul.real ∈ rationalHull (fractionRow199.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow199 rev199_plane38 rev199_vertex2 rev199_vertex1 rev199_s1_ul
    rev199_vertex2_mem rev199_vertex1_mem (by decide)
def rev199_s1_ur : FractionPoint := ⟨61399680052418983,228956070109600000,940526243324821263,1144780350548000000⟩
theorem rev199_s1_ur_mem : rev199_s1_ur.real ∈ rationalHull (fractionRow199.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow199 rev199_plane38 rev199_vertex2 rev199_vertex1 rev199_s1_ur
    rev199_vertex2_mem rev199_vertex1_mem (by decide)
theorem rev199_slab1 (p : Point) (hp : p∈IntegerCarrier rev199_planes)
    (hx0 : rev199_s1_ll.real.1≤p.1) (hx1 : p.1≤rev199_s1_lr.real.1) :
    p∈rationalHull (fractionRow199.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev199_plane34 rev199_plane38 rev199_s1_ll rev199_s1_lr rev199_s1_ul rev199_s1_ur
    (by decide) rev199_s1_ll_mem rev199_s1_lr_mem rev199_s1_ul_mem rev199_s1_ur_mem p
    (hp _ rev199_plane34_mem) (hp _ rev199_plane38_mem) hx0 hx1
theorem rev199_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev199_planes) : rev199_s0_ll.real.1≤p.1 := by
  have hc := rev199_plane38.combine_sound rev199_plane44 15204000000 699324000000 (by decide) (by decide) p
    (hp _ rev199_plane38_mem) (hp _ rev199_plane44_mem)
  exact (rev199_plane38.combine rev199_plane44 15204000000 699324000000).xBoundCheck_sound rev199_s0_ll.nx rev199_s0_ll.dx true (by decide) p hc
theorem rev199_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev199_planes) : p.1≤rev199_s1_lr.real.1 := by
  have hc := rev199_plane34.combine_sound rev199_plane38 699324000000 1440116000000 (by decide) (by decide) p
    (hp _ rev199_plane34_mem) (hp _ rev199_plane38_mem)
  exact (rev199_plane34.combine rev199_plane38 699324000000 1440116000000).xBoundCheck_sound rev199_s1_lr.nx rev199_s1_lr.dx false (by decide) p hc
theorem rev199_hull (p : Point) (hp : p∈IntegerCarrier rev199_planes) :
    p∈rationalHull (fractionRow199.map FractionPoint.rational) := by
  have hxlo := rev199_bound0_lo p hp
  have hxhi := rev199_bound0_hi p hp
  by_cases h0 : p.1≤rev199_s0_lr.real.1
  · exact rev199_slab0 p hp hxlo h0
  exact rev199_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull199 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,15,4,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow199 := by
  rw [← fractionRow199_correct]
  exact rev199_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull199
