import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks25
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev205_planes : List IntegerPlane := integerOverlayPlanes ![14,14,4,7]
def rev205_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev205_plane3_mem : rev205_plane3 ∈ rev205_planes := by decide
def rev205_plane17 : IntegerPlane := ⟨(-2083356000000),(-746024000000),(-1711863292059)⟩
theorem rev205_plane17_mem : rev205_plane17 ∈ rev205_planes := by decide
def rev205_plane75 : IntegerPlane := ⟨2112760000000,48252000000,1031002749085⟩
theorem rev205_plane75_mem : rev205_plane75 ∈ rev205_planes := by decide
def rev205_vertex0 : FractionPoint := fractionRow205[0]!
theorem rev205_vertex0_mem : rev205_vertex0∈fractionRow205 := by decide
def rev205_vertex1 : FractionPoint := fractionRow205[1]!
theorem rev205_vertex1_mem : rev205_vertex1∈fractionRow205 := by decide
def rev205_vertex2 : FractionPoint := fractionRow205[2]!
theorem rev205_vertex2_mem : rev205_vertex2∈fractionRow205 := by decide
def rev205_s0_ll : FractionPoint := ⟨965839292059,2083356000000,1,1⟩
theorem rev205_s0_ll_mem : rev205_s0_ll.real ∈ rationalHull (fractionRow205.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow205 rev205_plane17 rev205_vertex1 rev205_vertex2 rev205_s0_ll
    rev205_vertex1_mem rev205_vertex2_mem (by decide)
def rev205_s0_lr : FractionPoint := ⟨196550149817,422552000000,78466830965992179,78808483312000000⟩
theorem rev205_s0_lr_mem : rev205_s0_lr.real ∈ rationalHull (fractionRow205.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow205 rev205_plane17 rev205_vertex1 rev205_vertex2 rev205_s0_lr
    rev205_vertex1_mem rev205_vertex2_mem (by decide)
def rev205_s0_ul : FractionPoint := ⟨965839292059,2083356000000,1,1⟩
theorem rev205_s0_ul_mem : rev205_s0_ul.real ∈ rationalHull (fractionRow205.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow205 rev205_plane3 rev205_vertex1 rev205_vertex0 rev205_s0_ul
    rev205_vertex1_mem rev205_vertex0_mem (by decide)
def rev205_s0_ur : FractionPoint := ⟨196550149817,422552000000,1,1⟩
theorem rev205_s0_ur_mem : rev205_s0_ur.real ∈ rationalHull (fractionRow205.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow205 rev205_plane3 rev205_vertex1 rev205_vertex0 rev205_s0_ur
    rev205_vertex1_mem rev205_vertex0_mem (by decide)
theorem rev205_slab0 (p : Point) (hp : p∈IntegerCarrier rev205_planes)
    (hx0 : rev205_s0_ll.real.1≤p.1) (hx1 : p.1≤rev205_s0_lr.real.1) :
    p∈rationalHull (fractionRow205.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev205_plane17 rev205_plane3 rev205_s0_ll rev205_s0_lr rev205_s0_ul rev205_s0_ur
    (by decide) rev205_s0_ll_mem rev205_s0_lr_mem rev205_s0_ul_mem rev205_s0_ur_mem p
    (hp _ rev205_plane17_mem) (hp _ rev205_plane3_mem) hx0 hx1
def rev205_s1_ll : FractionPoint := ⟨196550149817,422552000000,78466830965992179,78808483312000000⟩
theorem rev205_s1_ll_mem : rev205_s1_ll.real ∈ rationalHull (fractionRow205.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow205 rev205_plane17 rev205_vertex1 rev205_vertex2 rev205_s1_ll
    rev205_vertex1_mem rev205_vertex2_mem (by decide)
def rev205_s1_lr : FractionPoint := ⟨171637991828739293,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev205_s1_lr_mem : rev205_s1_lr.real ∈ rationalHull (fractionRow205.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow205 rev205_plane17 rev205_vertex1 rev205_vertex2 rev205_s1_lr
    rev205_vertex1_mem rev205_vertex2_mem (by decide)
def rev205_s1_ul : FractionPoint := ⟨196550149817,422552000000,1,1⟩
theorem rev205_s1_ul_mem : rev205_s1_ul.real ∈ rationalHull (fractionRow205.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow205 rev205_plane75 rev205_vertex0 rev205_vertex2 rev205_s1_ul
    rev205_vertex0_mem rev205_vertex2_mem (by decide)
def rev205_s1_ur : FractionPoint := ⟨171637991828739293,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev205_s1_ur_mem : rev205_s1_ur.real ∈ rationalHull (fractionRow205.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow205 rev205_plane75 rev205_vertex0 rev205_vertex2 rev205_s1_ur
    rev205_vertex0_mem rev205_vertex2_mem (by decide)
theorem rev205_slab1 (p : Point) (hp : p∈IntegerCarrier rev205_planes)
    (hx0 : rev205_s1_ll.real.1≤p.1) (hx1 : p.1≤rev205_s1_lr.real.1) :
    p∈rationalHull (fractionRow205.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev205_plane17 rev205_plane75 rev205_s1_ll rev205_s1_lr rev205_s1_ul rev205_s1_ur
    (by decide) rev205_s1_ll_mem rev205_s1_lr_mem rev205_s1_ul_mem rev205_s1_ur_mem p
    (hp _ rev205_plane17_mem) (hp _ rev205_plane75_mem) hx0 hx1
theorem rev205_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev205_planes) : rev205_s0_ll.real.1≤p.1 := by
  have hc := rev205_plane3.combine_sound rev205_plane17 746024000000 1 (by decide) (by decide) p
    (hp _ rev205_plane3_mem) (hp _ rev205_plane17_mem)
  exact (rev205_plane3.combine rev205_plane17 746024000000 1).xBoundCheck_sound rev205_s0_ll.nx rev205_s0_ll.dx true (by decide) p hc
theorem rev205_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev205_planes) : p.1≤rev205_s1_lr.real.1 := by
  have hc := rev205_plane17.combine_sound rev205_plane75 48252000000 746024000000 (by decide) (by decide) p
    (hp _ rev205_plane17_mem) (hp _ rev205_plane75_mem)
  exact (rev205_plane17.combine rev205_plane75 48252000000 746024000000).xBoundCheck_sound rev205_s1_lr.nx rev205_s1_lr.dx false (by decide) p hc
theorem rev205_hull (p : Point) (hp : p∈IntegerCarrier rev205_planes) :
    p∈rationalHull (fractionRow205.map FractionPoint.rational) := by
  have hxlo := rev205_bound0_lo p hp
  have hxhi := rev205_bound0_hi p hp
  by_cases h0 : p.1≤rev205_s0_lr.real.1
  · exact rev205_slab0 p hp hxlo h0
  exact rev205_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull205 (p : Point)
    (hp : ∀ g, ClosedCell ((![14,14,4,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow205 := by
  rw [← fractionRow205_correct]
  exact rev205_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull205
