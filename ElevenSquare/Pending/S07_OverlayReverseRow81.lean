import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks10
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev81_planes : List IntegerPlane := integerOverlayPlanes ![6,6,6,9]
def rev81_plane9 : IntegerPlane := ⟨(-2112812000000),(-824716000000),(-1363770835544)⟩
theorem rev81_plane9_mem : rev81_plane9 ∈ rev81_planes := by decide
def rev81_plane13 : IntegerPlane := ⟨(-2164112000000),1343640000000,(-410236000000)⟩
theorem rev81_plane13_mem : rev81_plane13 ∈ rev81_planes := by decide
def rev81_plane29 : IntegerPlane := ⟨2112812000000,(-824716000000),749041164456⟩
theorem rev81_plane29_mem : rev81_plane29 ∈ rev81_planes := by decide
def rev81_plane33 : IntegerPlane := ⟨2164112000000,1343640000000,1753876000000⟩
theorem rev81_plane33_mem : rev81_plane33 ∈ rev81_planes := by decide
def rev81_vertex0 : FractionPoint := fractionRow81[0]!
theorem rev81_vertex0_mem : rev81_vertex0∈fractionRow81 := by decide
def rev81_vertex1 : FractionPoint := fractionRow81[1]!
theorem rev81_vertex1_mem : rev81_vertex1∈fractionRow81 := by decide
def rev81_vertex2 : FractionPoint := fractionRow81[2]!
theorem rev81_vertex2_mem : rev81_vertex2∈fractionRow81 := by decide
def rev81_vertex3 : FractionPoint := fractionRow81[3]!
theorem rev81_vertex3_mem : rev81_vertex3∈fractionRow81 := by decide
def rev81_s0_ll : FractionPoint := ⟨357030466849727,760466530900000,857155134382729,1901166327250000⟩
theorem rev81_s0_ll_mem : rev81_s0_ll.real ∈ rationalHull (fractionRow81.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow81 rev81_plane9 rev81_vertex1 rev81_vertex2 rev81_s0_ll
    rev81_vertex1_mem rev81_vertex2_mem (by decide)
def rev81_s0_lr : FractionPoint := ⟨1,2,38420604443,103089500000⟩
theorem rev81_s0_lr_mem : rev81_s0_lr.real ∈ rationalHull (fractionRow81.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow81 rev81_plane9 rev81_vertex1 rev81_vertex2 rev81_s0_lr
    rev81_vertex1_mem rev81_vertex2_mem (by decide)
def rev81_s0_ul : FractionPoint := ⟨357030466849727,760466530900000,857155134382729,1901166327250000⟩
theorem rev81_s0_ul_mem : rev81_s0_ul.real ∈ rationalHull (fractionRow81.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow81 rev81_plane13 rev81_vertex1 rev81_vertex0 rev81_s0_ul
    rev81_vertex1_mem rev81_vertex0_mem (by decide)
def rev81_s0_ur : FractionPoint := ⟨1,2,1,2⟩
theorem rev81_s0_ur_mem : rev81_s0_ur.real ∈ rationalHull (fractionRow81.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow81 rev81_plane13 rev81_vertex1 rev81_vertex0 rev81_s0_ur
    rev81_vertex1_mem rev81_vertex0_mem (by decide)
theorem rev81_slab0 (p : Point) (hp : p∈IntegerCarrier rev81_planes)
    (hx0 : rev81_s0_ll.real.1≤p.1) (hx1 : p.1≤rev81_s0_lr.real.1) :
    p∈rationalHull (fractionRow81.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev81_plane9 rev81_plane13 rev81_s0_ll rev81_s0_lr rev81_s0_ul rev81_s0_ur
    (by decide) rev81_s0_ll_mem rev81_s0_lr_mem rev81_s0_ul_mem rev81_s0_ur_mem p
    (hp _ rev81_plane9_mem) (hp _ rev81_plane13_mem) hx0 hx1
def rev81_s1_ll : FractionPoint := ⟨1,2,38420604443,103089500000⟩
theorem rev81_s1_ll_mem : rev81_s1_ll.real ∈ rationalHull (fractionRow81.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow81 rev81_plane29 rev81_vertex2 rev81_vertex3 rev81_s1_ll
    rev81_vertex2_mem rev81_vertex3_mem (by decide)
def rev81_s1_lr : FractionPoint := ⟨403436064050273,760466530900000,857155134382729,1901166327250000⟩
theorem rev81_s1_lr_mem : rev81_s1_lr.real ∈ rationalHull (fractionRow81.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow81 rev81_plane29 rev81_vertex2 rev81_vertex3 rev81_s1_lr
    rev81_vertex2_mem rev81_vertex3_mem (by decide)
def rev81_s1_ul : FractionPoint := ⟨1,2,1,2⟩
theorem rev81_s1_ul_mem : rev81_s1_ul.real ∈ rationalHull (fractionRow81.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow81 rev81_plane33 rev81_vertex0 rev81_vertex3 rev81_s1_ul
    rev81_vertex0_mem rev81_vertex3_mem (by decide)
def rev81_s1_ur : FractionPoint := ⟨403436064050273,760466530900000,857155134382729,1901166327250000⟩
theorem rev81_s1_ur_mem : rev81_s1_ur.real ∈ rationalHull (fractionRow81.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow81 rev81_plane33 rev81_vertex0 rev81_vertex3 rev81_s1_ur
    rev81_vertex0_mem rev81_vertex3_mem (by decide)
theorem rev81_slab1 (p : Point) (hp : p∈IntegerCarrier rev81_planes)
    (hx0 : rev81_s1_ll.real.1≤p.1) (hx1 : p.1≤rev81_s1_lr.real.1) :
    p∈rationalHull (fractionRow81.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev81_plane29 rev81_plane33 rev81_s1_ll rev81_s1_lr rev81_s1_ul rev81_s1_ur
    (by decide) rev81_s1_ll_mem rev81_s1_lr_mem rev81_s1_ul_mem rev81_s1_ur_mem p
    (hp _ rev81_plane29_mem) (hp _ rev81_plane33_mem) hx0 hx1
theorem rev81_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev81_planes) : rev81_s0_ll.real.1≤p.1 := by
  have hc := rev81_plane9.combine_sound rev81_plane13 1343640000000 824716000000 (by decide) (by decide) p
    (hp _ rev81_plane9_mem) (hp _ rev81_plane13_mem)
  exact (rev81_plane9.combine rev81_plane13 1343640000000 824716000000).xBoundCheck_sound rev81_s0_ll.nx rev81_s0_ll.dx true (by decide) p hc
theorem rev81_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev81_planes) : p.1≤rev81_s1_lr.real.1 := by
  have hc := rev81_plane29.combine_sound rev81_plane33 1343640000000 824716000000 (by decide) (by decide) p
    (hp _ rev81_plane29_mem) (hp _ rev81_plane33_mem)
  exact (rev81_plane29.combine rev81_plane33 1343640000000 824716000000).xBoundCheck_sound rev81_s1_lr.nx rev81_s1_lr.dx false (by decide) p hc
theorem rev81_hull (p : Point) (hp : p∈IntegerCarrier rev81_planes) :
    p∈rationalHull (fractionRow81.map FractionPoint.rational) := by
  have hxlo := rev81_bound0_lo p hp
  have hxhi := rev81_bound0_hi p hp
  by_cases h0 : p.1≤rev81_s0_lr.real.1
  · exact rev81_slab0 p hp hxlo h0
  exact rev81_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull81 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,6,6,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow81 := by
  rw [← fractionRow81_correct]
  exact rev81_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull81
