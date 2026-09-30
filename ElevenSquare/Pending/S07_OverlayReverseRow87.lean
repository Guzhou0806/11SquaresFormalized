import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks10
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev87_planes : List IntegerPlane := integerOverlayPlanes ![6,9,9,9]
def rev87_plane13 : IntegerPlane := ⟨(-2164112000000),1343640000000,(-410236000000)⟩
theorem rev87_plane13_mem : rev87_plane13 ∈ rev87_planes := by decide
def rev87_plane30 : IntegerPlane := ⟨(-2164112000000),(-1343640000000),(-1753876000000)⟩
theorem rev87_plane30_mem : rev87_plane30 ∈ rev87_planes := by decide
def rev87_plane50 : IntegerPlane := ⟨(-1343640000000),(-2164112000000),(-1753876000000)⟩
theorem rev87_plane50_mem : rev87_plane50 ∈ rev87_planes := by decide
def rev87_plane54 : IntegerPlane := ⟨824716000000,(-2112812000000),(-539054835544)⟩
theorem rev87_plane54_mem : rev87_plane54 ∈ rev87_planes := by decide
def rev87_plane70 : IntegerPlane := ⟨(-1343640000000),2164112000000,410236000000⟩
theorem rev87_plane70_mem : rev87_plane70 ∈ rev87_planes := by decide
def rev87_plane74 : IntegerPlane := ⟨824716000000,2112812000000,1573757164456⟩
theorem rev87_plane74_mem : rev87_plane74 ∈ rev87_planes := by decide
def rev87_vertex0 : FractionPoint := fractionRow87[0]!
theorem rev87_vertex0_mem : rev87_vertex0∈fractionRow87 := by decide
def rev87_vertex1 : FractionPoint := fractionRow87[1]!
theorem rev87_vertex1_mem : rev87_vertex1∈fractionRow87 := by decide
def rev87_vertex2 : FractionPoint := fractionRow87[2]!
theorem rev87_vertex2_mem : rev87_vertex2∈fractionRow87 := by decide
def rev87_vertex3 : FractionPoint := fractionRow87[3]!
theorem rev87_vertex3_mem : rev87_vertex3∈fractionRow87 := by decide
def rev87_s0_ll : FractionPoint := ⟨1,2,1,2⟩
theorem rev87_s0_ll_mem : rev87_s0_ll.real ∈ rationalHull (fractionRow87.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow87 rev87_plane50 rev87_vertex0 rev87_vertex1 rev87_s0_ll
    rev87_vertex0_mem rev87_vertex1_mem (by decide)
def rev87_s0_lr : FractionPoint := ⟨1044011192867271,1901166327250000,357030466849727,760466530900000⟩
theorem rev87_s0_lr_mem : rev87_s0_lr.real ∈ rationalHull (fractionRow87.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow87 rev87_plane50 rev87_vertex0 rev87_vertex1 rev87_s0_lr
    rev87_vertex0_mem rev87_vertex1_mem (by decide)
def rev87_s0_ul : FractionPoint := ⟨1,2,1,2⟩
theorem rev87_s0_ul_mem : rev87_s0_ul.real ∈ rationalHull (fractionRow87.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow87 rev87_plane70 rev87_vertex0 rev87_vertex3 rev87_s0_ul
    rev87_vertex0_mem rev87_vertex3_mem (by decide)
def rev87_s0_ur : FractionPoint := ⟨1044011192867271,1901166327250000,403436064050273,760466530900000⟩
theorem rev87_s0_ur_mem : rev87_s0_ur.real ∈ rationalHull (fractionRow87.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow87 rev87_plane70 rev87_vertex0 rev87_vertex3 rev87_s0_ur
    rev87_vertex0_mem rev87_vertex3_mem (by decide)
theorem rev87_slab0 (p : Point) (hp : p∈IntegerCarrier rev87_planes)
    (hx0 : rev87_s0_ll.real.1≤p.1) (hx1 : p.1≤rev87_s0_lr.real.1) :
    p∈rationalHull (fractionRow87.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev87_plane50 rev87_plane70 rev87_s0_ll rev87_s0_lr rev87_s0_ul rev87_s0_ur
    (by decide) rev87_s0_ll_mem rev87_s0_lr_mem rev87_s0_ul_mem rev87_s0_ur_mem p
    (hp _ rev87_plane50_mem) (hp _ rev87_plane70_mem) hx0 hx1
def rev87_s1_ll : FractionPoint := ⟨1044011192867271,1901166327250000,357030466849727,760466530900000⟩
theorem rev87_s1_ll_mem : rev87_s1_ll.real ∈ rationalHull (fractionRow87.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow87 rev87_plane54 rev87_vertex1 rev87_vertex2 rev87_s1_ll
    rev87_vertex1_mem rev87_vertex2_mem (by decide)
def rev87_s1_lr : FractionPoint := ⟨64668895557,103089500000,1,2⟩
theorem rev87_s1_lr_mem : rev87_s1_lr.real ∈ rationalHull (fractionRow87.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow87 rev87_plane54 rev87_vertex1 rev87_vertex2 rev87_s1_lr
    rev87_vertex1_mem rev87_vertex2_mem (by decide)
def rev87_s1_ul : FractionPoint := ⟨1044011192867271,1901166327250000,403436064050273,760466530900000⟩
theorem rev87_s1_ul_mem : rev87_s1_ul.real ∈ rationalHull (fractionRow87.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow87 rev87_plane74 rev87_vertex3 rev87_vertex2 rev87_s1_ul
    rev87_vertex3_mem rev87_vertex2_mem (by decide)
def rev87_s1_ur : FractionPoint := ⟨64668895557,103089500000,1,2⟩
theorem rev87_s1_ur_mem : rev87_s1_ur.real ∈ rationalHull (fractionRow87.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow87 rev87_plane74 rev87_vertex3 rev87_vertex2 rev87_s1_ur
    rev87_vertex3_mem rev87_vertex2_mem (by decide)
theorem rev87_slab1 (p : Point) (hp : p∈IntegerCarrier rev87_planes)
    (hx0 : rev87_s1_ll.real.1≤p.1) (hx1 : p.1≤rev87_s1_lr.real.1) :
    p∈rationalHull (fractionRow87.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev87_plane54 rev87_plane74 rev87_s1_ll rev87_s1_lr rev87_s1_ul rev87_s1_ur
    (by decide) rev87_s1_ll_mem rev87_s1_lr_mem rev87_s1_ul_mem rev87_s1_ur_mem p
    (hp _ rev87_plane54_mem) (hp _ rev87_plane74_mem) hx0 hx1
theorem rev87_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev87_planes) : rev87_s0_ll.real.1≤p.1 := by
  have hc := rev87_plane13.combine_sound rev87_plane30 1343640000000 1343640000000 (by decide) (by decide) p
    (hp _ rev87_plane13_mem) (hp _ rev87_plane30_mem)
  exact (rev87_plane13.combine rev87_plane30 1343640000000 1343640000000).xBoundCheck_sound rev87_s0_ll.nx rev87_s0_ll.dx true (by decide) p hc
theorem rev87_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev87_planes) : p.1≤rev87_s1_lr.real.1 := by
  have hc := rev87_plane54.combine_sound rev87_plane74 2112812000000 2112812000000 (by decide) (by decide) p
    (hp _ rev87_plane54_mem) (hp _ rev87_plane74_mem)
  exact (rev87_plane54.combine rev87_plane74 2112812000000 2112812000000).xBoundCheck_sound rev87_s1_lr.nx rev87_s1_lr.dx false (by decide) p hc
theorem rev87_hull (p : Point) (hp : p∈IntegerCarrier rev87_planes) :
    p∈rationalHull (fractionRow87.map FractionPoint.rational) := by
  have hxlo := rev87_bound0_lo p hp
  have hxhi := rev87_bound0_hi p hp
  by_cases h0 : p.1≤rev87_s0_lr.real.1
  · exact rev87_slab0 p hp hxlo h0
  exact rev87_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull87 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,9,9,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow87 := by
  rw [← fractionRow87_correct]
  exact rev87_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull87
