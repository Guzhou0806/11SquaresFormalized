import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks17
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev138_planes : List IntegerPlane := integerOverlayPlanes ![9,9,9,6]
def rev138_plane10 : IntegerPlane := ⟨2164112000000,(-1343640000000),410236000000⟩
theorem rev138_plane10_mem : rev138_plane10 ∈ rev138_planes := by decide
def rev138_plane14 : IntegerPlane := ⟨2112812000000,824716000000,1573757164456⟩
theorem rev138_plane14_mem : rev138_plane14 ∈ rev138_planes := by decide
def rev138_plane30 : IntegerPlane := ⟨(-2164112000000),(-1343640000000),(-1753876000000)⟩
theorem rev138_plane30_mem : rev138_plane30 ∈ rev138_planes := by decide
def rev138_plane34 : IntegerPlane := ⟨(-2112812000000),824716000000,(-539054835544)⟩
theorem rev138_plane34_mem : rev138_plane34 ∈ rev138_planes := by decide
def rev138_vertex0 : FractionPoint := fractionRow138[0]!
theorem rev138_vertex0_mem : rev138_vertex0∈fractionRow138 := by decide
def rev138_vertex1 : FractionPoint := fractionRow138[1]!
theorem rev138_vertex1_mem : rev138_vertex1∈fractionRow138 := by decide
def rev138_vertex2 : FractionPoint := fractionRow138[2]!
theorem rev138_vertex2_mem : rev138_vertex2∈fractionRow138 := by decide
def rev138_vertex3 : FractionPoint := fractionRow138[3]!
theorem rev138_vertex3_mem : rev138_vertex3∈fractionRow138 := by decide
def rev138_s0_ll : FractionPoint := ⟨357030466849727,760466530900000,1044011192867271,1901166327250000⟩
theorem rev138_s0_ll_mem : rev138_s0_ll.real ∈ rationalHull (fractionRow138.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow138 rev138_plane30 rev138_vertex3 rev138_vertex0 rev138_s0_ll
    rev138_vertex3_mem rev138_vertex0_mem (by decide)
def rev138_s0_lr : FractionPoint := ⟨1,2,1,2⟩
theorem rev138_s0_lr_mem : rev138_s0_lr.real ∈ rationalHull (fractionRow138.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow138 rev138_plane30 rev138_vertex3 rev138_vertex0 rev138_s0_lr
    rev138_vertex3_mem rev138_vertex0_mem (by decide)
def rev138_s0_ul : FractionPoint := ⟨357030466849727,760466530900000,1044011192867271,1901166327250000⟩
theorem rev138_s0_ul_mem : rev138_s0_ul.real ∈ rationalHull (fractionRow138.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow138 rev138_plane34 rev138_vertex3 rev138_vertex2 rev138_s0_ul
    rev138_vertex3_mem rev138_vertex2_mem (by decide)
def rev138_s0_ur : FractionPoint := ⟨1,2,64668895557,103089500000⟩
theorem rev138_s0_ur_mem : rev138_s0_ur.real ∈ rationalHull (fractionRow138.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow138 rev138_plane34 rev138_vertex3 rev138_vertex2 rev138_s0_ur
    rev138_vertex3_mem rev138_vertex2_mem (by decide)
theorem rev138_slab0 (p : Point) (hp : p∈IntegerCarrier rev138_planes)
    (hx0 : rev138_s0_ll.real.1≤p.1) (hx1 : p.1≤rev138_s0_lr.real.1) :
    p∈rationalHull (fractionRow138.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev138_plane30 rev138_plane34 rev138_s0_ll rev138_s0_lr rev138_s0_ul rev138_s0_ur
    (by decide) rev138_s0_ll_mem rev138_s0_lr_mem rev138_s0_ul_mem rev138_s0_ur_mem p
    (hp _ rev138_plane30_mem) (hp _ rev138_plane34_mem) hx0 hx1
def rev138_s1_ll : FractionPoint := ⟨1,2,1,2⟩
theorem rev138_s1_ll_mem : rev138_s1_ll.real ∈ rationalHull (fractionRow138.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow138 rev138_plane10 rev138_vertex0 rev138_vertex1 rev138_s1_ll
    rev138_vertex0_mem rev138_vertex1_mem (by decide)
def rev138_s1_lr : FractionPoint := ⟨403436064050273,760466530900000,1044011192867271,1901166327250000⟩
theorem rev138_s1_lr_mem : rev138_s1_lr.real ∈ rationalHull (fractionRow138.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow138 rev138_plane10 rev138_vertex0 rev138_vertex1 rev138_s1_lr
    rev138_vertex0_mem rev138_vertex1_mem (by decide)
def rev138_s1_ul : FractionPoint := ⟨1,2,64668895557,103089500000⟩
theorem rev138_s1_ul_mem : rev138_s1_ul.real ∈ rationalHull (fractionRow138.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow138 rev138_plane14 rev138_vertex2 rev138_vertex1 rev138_s1_ul
    rev138_vertex2_mem rev138_vertex1_mem (by decide)
def rev138_s1_ur : FractionPoint := ⟨403436064050273,760466530900000,1044011192867271,1901166327250000⟩
theorem rev138_s1_ur_mem : rev138_s1_ur.real ∈ rationalHull (fractionRow138.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow138 rev138_plane14 rev138_vertex2 rev138_vertex1 rev138_s1_ur
    rev138_vertex2_mem rev138_vertex1_mem (by decide)
theorem rev138_slab1 (p : Point) (hp : p∈IntegerCarrier rev138_planes)
    (hx0 : rev138_s1_ll.real.1≤p.1) (hx1 : p.1≤rev138_s1_lr.real.1) :
    p∈rationalHull (fractionRow138.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev138_plane10 rev138_plane14 rev138_s1_ll rev138_s1_lr rev138_s1_ul rev138_s1_ur
    (by decide) rev138_s1_ll_mem rev138_s1_lr_mem rev138_s1_ul_mem rev138_s1_ur_mem p
    (hp _ rev138_plane10_mem) (hp _ rev138_plane14_mem) hx0 hx1
theorem rev138_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev138_planes) : rev138_s0_ll.real.1≤p.1 := by
  have hc := rev138_plane30.combine_sound rev138_plane34 824716000000 1343640000000 (by decide) (by decide) p
    (hp _ rev138_plane30_mem) (hp _ rev138_plane34_mem)
  exact (rev138_plane30.combine rev138_plane34 824716000000 1343640000000).xBoundCheck_sound rev138_s0_ll.nx rev138_s0_ll.dx true (by decide) p hc
theorem rev138_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev138_planes) : p.1≤rev138_s1_lr.real.1 := by
  have hc := rev138_plane10.combine_sound rev138_plane14 824716000000 1343640000000 (by decide) (by decide) p
    (hp _ rev138_plane10_mem) (hp _ rev138_plane14_mem)
  exact (rev138_plane10.combine rev138_plane14 824716000000 1343640000000).xBoundCheck_sound rev138_s1_lr.nx rev138_s1_lr.dx false (by decide) p hc
theorem rev138_hull (p : Point) (hp : p∈IntegerCarrier rev138_planes) :
    p∈rationalHull (fractionRow138.map FractionPoint.rational) := by
  have hxlo := rev138_bound0_lo p hp
  have hxhi := rev138_bound0_hi p hp
  by_cases h0 : p.1≤rev138_s0_lr.real.1
  · exact rev138_slab0 p hp hxlo h0
  exact rev138_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull138 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,9,9,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow138 := by
  rw [← fractionRow138_correct]
  exact rev138_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull138
