import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks22
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev176_planes : List IntegerPlane := integerOverlayPlanes ![11,8,13,15]
def rev176_plane19 : IntegerPlane := ⟨(-15204000000),2139684000000,1555517771568⟩
theorem rev176_plane19_mem : rev176_plane19 ∈ rev176_planes := by decide
def rev176_plane74 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-2741459880216)⟩
theorem rev176_plane74_mem : rev176_plane74 ∈ rev176_planes := by decide
def rev176_plane78 : IntegerPlane := ⟨699324000000,(-2145688000000),(-995724727641)⟩
theorem rev176_plane78_mem : rev176_plane78 ∈ rev176_planes := by decide
def rev176_vertex0 : FractionPoint := fractionRow176[0]!
theorem rev176_vertex0_mem : rev176_vertex0∈fractionRow176 := by decide
def rev176_vertex1 : FractionPoint := fractionRow176[1]!
theorem rev176_vertex1_mem : rev176_vertex1∈fractionRow176 := by decide
def rev176_vertex2 : FractionPoint := fractionRow176[2]!
theorem rev176_vertex2_mem : rev176_vertex2∈fractionRow176 := by decide
def rev176_s0_ll : FractionPoint := ⟨26600718365166711,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev176_s0_ll_mem : rev176_s0_ll.real ∈ rationalHull (fractionRow176.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow176 rev176_plane74 rev176_vertex1 rev176_vertex2 rev176_s0_ll
    rev176_vertex1_mem rev176_vertex2_mem (by decide)
def rev176_s0_lr : FractionPoint := ⟨940526243324821263,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev176_s0_lr_mem : rev176_s0_lr.real ∈ rationalHull (fractionRow176.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow176 rev176_plane74 rev176_vertex1 rev176_vertex2 rev176_s0_lr
    rev176_vertex1_mem rev176_vertex2_mem (by decide)
def rev176_s0_ul : FractionPoint := ⟨26600718365166711,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev176_s0_ul_mem : rev176_s0_ul.real ∈ rationalHull (fractionRow176.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow176 rev176_plane19 rev176_vertex1 rev176_vertex0 rev176_s0_ul
    rev176_vertex1_mem rev176_vertex0_mem (by decide)
def rev176_s0_ur : FractionPoint := ⟨940526243324821263,1144780350548000000,149585495068564117508493,204122349965162236000000⟩
theorem rev176_s0_ur_mem : rev176_s0_ur.real ∈ rationalHull (fractionRow176.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow176 rev176_plane19 rev176_vertex1 rev176_vertex0 rev176_s0_ur
    rev176_vertex1_mem rev176_vertex0_mem (by decide)
theorem rev176_slab0 (p : Point) (hp : p∈IntegerCarrier rev176_planes)
    (hx0 : rev176_s0_ll.real.1≤p.1) (hx1 : p.1≤rev176_s0_lr.real.1) :
    p∈rationalHull (fractionRow176.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev176_plane74 rev176_plane19 rev176_s0_ll rev176_s0_lr rev176_s0_ul rev176_s0_ur
    (by decide) rev176_s0_ll_mem rev176_s0_lr_mem rev176_s0_ul_mem rev176_s0_ur_mem p
    (hp _ rev176_plane74_mem) (hp _ rev176_plane19_mem) hx0 hx1
def rev176_s1_ll : FractionPoint := ⟨940526243324821263,1144780350548000000,167556390057181017,228956070109600000⟩
theorem rev176_s1_ll_mem : rev176_s1_ll.real ∈ rationalHull (fractionRow176.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow176 rev176_plane78 rev176_vertex2 rev176_vertex0 rev176_s1_ll
    rev176_vertex2_mem rev176_vertex0_mem (by decide)
def rev176_s1_lr : FractionPoint := ⟨20118659135039889,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev176_s1_lr_mem : rev176_s1_lr.real ∈ rationalHull (fractionRow176.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow176 rev176_plane78 rev176_vertex2 rev176_vertex0 rev176_s1_lr
    rev176_vertex2_mem rev176_vertex0_mem (by decide)
def rev176_s1_ul : FractionPoint := ⟨940526243324821263,1144780350548000000,149585495068564117508493,204122349965162236000000⟩
theorem rev176_s1_ul_mem : rev176_s1_ul.real ∈ rationalHull (fractionRow176.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow176 rev176_plane19 rev176_vertex1 rev176_vertex0 rev176_s1_ul
    rev176_vertex1_mem rev176_vertex0_mem (by decide)
def rev176_s1_ur : FractionPoint := ⟨20118659135039889,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev176_s1_ur_mem : rev176_s1_ur.real ∈ rationalHull (fractionRow176.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow176 rev176_plane19 rev176_vertex1 rev176_vertex0 rev176_s1_ur
    rev176_vertex1_mem rev176_vertex0_mem (by decide)
theorem rev176_slab1 (p : Point) (hp : p∈IntegerCarrier rev176_planes)
    (hx0 : rev176_s1_ll.real.1≤p.1) (hx1 : p.1≤rev176_s1_lr.real.1) :
    p∈rationalHull (fractionRow176.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev176_plane78 rev176_plane19 rev176_s1_ll rev176_s1_lr rev176_s1_ul rev176_s1_ur
    (by decide) rev176_s1_ll_mem rev176_s1_lr_mem rev176_s1_ul_mem rev176_s1_ur_mem p
    (hp _ rev176_plane78_mem) (hp _ rev176_plane19_mem) hx0 hx1
theorem rev176_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev176_planes) : rev176_s0_ll.real.1≤p.1 := by
  have hc := rev176_plane19.combine_sound rev176_plane74 2129316000000 2139684000000 (by decide) (by decide) p
    (hp _ rev176_plane19_mem) (hp _ rev176_plane74_mem)
  exact (rev176_plane19.combine rev176_plane74 2129316000000 2139684000000).xBoundCheck_sound rev176_s0_ll.nx rev176_s0_ll.dx true (by decide) p hc
theorem rev176_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev176_planes) : p.1≤rev176_s1_lr.real.1 := by
  have hc := rev176_plane19.combine_sound rev176_plane78 2145688000000 2139684000000 (by decide) (by decide) p
    (hp _ rev176_plane19_mem) (hp _ rev176_plane78_mem)
  exact (rev176_plane19.combine rev176_plane78 2145688000000 2139684000000).xBoundCheck_sound rev176_s1_lr.nx rev176_s1_lr.dx false (by decide) p hc
theorem rev176_hull (p : Point) (hp : p∈IntegerCarrier rev176_planes) :
    p∈rationalHull (fractionRow176.map FractionPoint.rational) := by
  have hxlo := rev176_bound0_lo p hp
  have hxhi := rev176_bound0_hi p hp
  by_cases h0 : p.1≤rev176_s0_lr.real.1
  · exact rev176_slab0 p hp hxlo h0
  exact rev176_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull176 (p : Point)
    (hp : ∀ g, ClosedCell ((![11,8,13,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow176 := by
  rw [← fractionRow176_correct]
  exact rev176_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull176
