import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks1
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev14_planes : List IntegerPlane := integerOverlayPlanes ![1,1,11,8]
def rev14_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev14_plane2_mem : rev14_plane2 ∈ rev14_planes := by decide
def rev14_plane6 : IntegerPlane := ⟨2083356000000,746024000000,1117516707941⟩
theorem rev14_plane6_mem : rev14_plane6 ∈ rev14_planes := by decide
def rev14_plane68 : IntegerPlane := ⟨(-2112760000000),(-48252000000),(-1130009250915)⟩
theorem rev14_plane68_mem : rev14_plane68 ∈ rev14_planes := by decide
def rev14_vertex0 : FractionPoint := fractionRow14[0]!
theorem rev14_vertex0_mem : rev14_vertex0∈fractionRow14 := by decide
def rev14_vertex1 : FractionPoint := fractionRow14[1]!
theorem rev14_vertex1_mem : rev14_vertex1∈fractionRow14 := by decide
def rev14_vertex2 : FractionPoint := fractionRow14[2]!
theorem rev14_vertex2_mem : rev14_vertex2∈fractionRow14 := by decide
def rev14_s0_ll : FractionPoint := ⟨197272901303260707,368910893132000000,341652346007821,73782178626400000⟩
theorem rev14_s0_ll_mem : rev14_s0_ll.real ∈ rationalHull (fractionRow14.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow14 rev14_plane68 rev14_vertex2 rev14_vertex0 rev14_s0_ll
    rev14_vertex2_mem rev14_vertex0_mem (by decide)
def rev14_s0_lr : FractionPoint := ⟨226001850183,422552000000,0,1⟩
theorem rev14_s0_lr_mem : rev14_s0_lr.real ∈ rationalHull (fractionRow14.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow14 rev14_plane68 rev14_vertex2 rev14_vertex0 rev14_s0_lr
    rev14_vertex2_mem rev14_vertex0_mem (by decide)
def rev14_s0_ul : FractionPoint := ⟨197272901303260707,368910893132000000,341652346007821,73782178626400000⟩
theorem rev14_s0_ul_mem : rev14_s0_ul.real ∈ rationalHull (fractionRow14.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow14 rev14_plane6 rev14_vertex2 rev14_vertex1 rev14_s0_ul
    rev14_vertex2_mem rev14_vertex1_mem (by decide)
def rev14_s0_ur : FractionPoint := ⟨226001850183,422552000000,341652346007821,78808483312000000⟩
theorem rev14_s0_ur_mem : rev14_s0_ur.real ∈ rationalHull (fractionRow14.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow14 rev14_plane6 rev14_vertex2 rev14_vertex1 rev14_s0_ur
    rev14_vertex2_mem rev14_vertex1_mem (by decide)
theorem rev14_slab0 (p : Point) (hp : p∈IntegerCarrier rev14_planes)
    (hx0 : rev14_s0_ll.real.1≤p.1) (hx1 : p.1≤rev14_s0_lr.real.1) :
    p∈rationalHull (fractionRow14.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev14_plane68 rev14_plane6 rev14_s0_ll rev14_s0_lr rev14_s0_ul rev14_s0_ur
    (by decide) rev14_s0_ll_mem rev14_s0_lr_mem rev14_s0_ul_mem rev14_s0_ur_mem p
    (hp _ rev14_plane68_mem) (hp _ rev14_plane6_mem) hx0 hx1
def rev14_s1_ll : FractionPoint := ⟨226001850183,422552000000,0,1⟩
theorem rev14_s1_ll_mem : rev14_s1_ll.real ∈ rationalHull (fractionRow14.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow14 rev14_plane2 rev14_vertex0 rev14_vertex1 rev14_s1_ll
    rev14_vertex0_mem rev14_vertex1_mem (by decide)
def rev14_s1_lr : FractionPoint := ⟨1117516707941,2083356000000,0,1⟩
theorem rev14_s1_lr_mem : rev14_s1_lr.real ∈ rationalHull (fractionRow14.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow14 rev14_plane2 rev14_vertex0 rev14_vertex1 rev14_s1_lr
    rev14_vertex0_mem rev14_vertex1_mem (by decide)
def rev14_s1_ul : FractionPoint := ⟨226001850183,422552000000,341652346007821,78808483312000000⟩
theorem rev14_s1_ul_mem : rev14_s1_ul.real ∈ rationalHull (fractionRow14.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow14 rev14_plane6 rev14_vertex2 rev14_vertex1 rev14_s1_ul
    rev14_vertex2_mem rev14_vertex1_mem (by decide)
def rev14_s1_ur : FractionPoint := ⟨1117516707941,2083356000000,0,1⟩
theorem rev14_s1_ur_mem : rev14_s1_ur.real ∈ rationalHull (fractionRow14.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow14 rev14_plane6 rev14_vertex2 rev14_vertex1 rev14_s1_ur
    rev14_vertex2_mem rev14_vertex1_mem (by decide)
theorem rev14_slab1 (p : Point) (hp : p∈IntegerCarrier rev14_planes)
    (hx0 : rev14_s1_ll.real.1≤p.1) (hx1 : p.1≤rev14_s1_lr.real.1) :
    p∈rationalHull (fractionRow14.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev14_plane2 rev14_plane6 rev14_s1_ll rev14_s1_lr rev14_s1_ul rev14_s1_ur
    (by decide) rev14_s1_ll_mem rev14_s1_lr_mem rev14_s1_ul_mem rev14_s1_ur_mem p
    (hp _ rev14_plane2_mem) (hp _ rev14_plane6_mem) hx0 hx1
theorem rev14_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev14_planes) : rev14_s0_ll.real.1≤p.1 := by
  have hc := rev14_plane6.combine_sound rev14_plane68 48252000000 746024000000 (by decide) (by decide) p
    (hp _ rev14_plane6_mem) (hp _ rev14_plane68_mem)
  exact (rev14_plane6.combine rev14_plane68 48252000000 746024000000).xBoundCheck_sound rev14_s0_ll.nx rev14_s0_ll.dx true (by decide) p hc
theorem rev14_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev14_planes) : p.1≤rev14_s1_lr.real.1 := by
  have hc := rev14_plane2.combine_sound rev14_plane6 746024000000 1 (by decide) (by decide) p
    (hp _ rev14_plane2_mem) (hp _ rev14_plane6_mem)
  exact (rev14_plane2.combine rev14_plane6 746024000000 1).xBoundCheck_sound rev14_s1_lr.nx rev14_s1_lr.dx false (by decide) p hc
theorem rev14_hull (p : Point) (hp : p∈IntegerCarrier rev14_planes) :
    p∈rationalHull (fractionRow14.map FractionPoint.rational) := by
  have hxlo := rev14_bound0_lo p hp
  have hxhi := rev14_bound0_hi p hp
  by_cases h0 : p.1≤rev14_s0_lr.real.1
  · exact rev14_slab0 p hp hxlo h0
  exact rev14_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull14 (p : Point)
    (hp : ∀ g, ClosedCell ((![1,1,11,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow14 := by
  rw [← fractionRow14_correct]
  exact rev14_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull14
