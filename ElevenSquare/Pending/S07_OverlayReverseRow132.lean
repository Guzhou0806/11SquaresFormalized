import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks16
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev132_planes : List IntegerPlane := integerOverlayPlanes ![9,6,6,6]
def rev132_plane10 : IntegerPlane := ⟨2164112000000,(-1343640000000),410236000000⟩
theorem rev132_plane10_mem : rev132_plane10 ∈ rev132_planes := by decide
def rev132_plane33 : IntegerPlane := ⟨2164112000000,1343640000000,1753876000000⟩
theorem rev132_plane33_mem : rev132_plane33 ∈ rev132_planes := by decide
def rev132_plane49 : IntegerPlane := ⟨(-824716000000),2112812000000,749041164456⟩
theorem rev132_plane49_mem : rev132_plane49 ∈ rev132_planes := by decide
def rev132_plane53 : IntegerPlane := ⟨1343640000000,2164112000000,1753876000000⟩
theorem rev132_plane53_mem : rev132_plane53 ∈ rev132_planes := by decide
def rev132_plane69 : IntegerPlane := ⟨(-824716000000),(-2112812000000),(-1363770835544)⟩
theorem rev132_plane69_mem : rev132_plane69 ∈ rev132_planes := by decide
def rev132_plane73 : IntegerPlane := ⟨1343640000000,(-2164112000000),(-410236000000)⟩
theorem rev132_plane73_mem : rev132_plane73 ∈ rev132_planes := by decide
def rev132_vertex0 : FractionPoint := fractionRow132[0]!
theorem rev132_vertex0_mem : rev132_vertex0∈fractionRow132 := by decide
def rev132_vertex1 : FractionPoint := fractionRow132[1]!
theorem rev132_vertex1_mem : rev132_vertex1∈fractionRow132 := by decide
def rev132_vertex2 : FractionPoint := fractionRow132[2]!
theorem rev132_vertex2_mem : rev132_vertex2∈fractionRow132 := by decide
def rev132_vertex3 : FractionPoint := fractionRow132[3]!
theorem rev132_vertex3_mem : rev132_vertex3∈fractionRow132 := by decide
def rev132_s0_ll : FractionPoint := ⟨38420604443,103089500000,1,2⟩
theorem rev132_s0_ll_mem : rev132_s0_ll.real ∈ rationalHull (fractionRow132.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow132 rev132_plane69 rev132_vertex2 rev132_vertex3 rev132_s0_ll
    rev132_vertex2_mem rev132_vertex3_mem (by decide)
def rev132_s0_lr : FractionPoint := ⟨857155134382729,1901166327250000,357030466849727,760466530900000⟩
theorem rev132_s0_lr_mem : rev132_s0_lr.real ∈ rationalHull (fractionRow132.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow132 rev132_plane69 rev132_vertex2 rev132_vertex3 rev132_s0_lr
    rev132_vertex2_mem rev132_vertex3_mem (by decide)
def rev132_s0_ul : FractionPoint := ⟨38420604443,103089500000,1,2⟩
theorem rev132_s0_ul_mem : rev132_s0_ul.real ∈ rationalHull (fractionRow132.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow132 rev132_plane49 rev132_vertex2 rev132_vertex1 rev132_s0_ul
    rev132_vertex2_mem rev132_vertex1_mem (by decide)
def rev132_s0_ur : FractionPoint := ⟨857155134382729,1901166327250000,403436064050273,760466530900000⟩
theorem rev132_s0_ur_mem : rev132_s0_ur.real ∈ rationalHull (fractionRow132.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow132 rev132_plane49 rev132_vertex2 rev132_vertex1 rev132_s0_ur
    rev132_vertex2_mem rev132_vertex1_mem (by decide)
theorem rev132_slab0 (p : Point) (hp : p∈IntegerCarrier rev132_planes)
    (hx0 : rev132_s0_ll.real.1≤p.1) (hx1 : p.1≤rev132_s0_lr.real.1) :
    p∈rationalHull (fractionRow132.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev132_plane69 rev132_plane49 rev132_s0_ll rev132_s0_lr rev132_s0_ul rev132_s0_ur
    (by decide) rev132_s0_ll_mem rev132_s0_lr_mem rev132_s0_ul_mem rev132_s0_ur_mem p
    (hp _ rev132_plane69_mem) (hp _ rev132_plane49_mem) hx0 hx1
def rev132_s1_ll : FractionPoint := ⟨857155134382729,1901166327250000,357030466849727,760466530900000⟩
theorem rev132_s1_ll_mem : rev132_s1_ll.real ∈ rationalHull (fractionRow132.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow132 rev132_plane73 rev132_vertex3 rev132_vertex0 rev132_s1_ll
    rev132_vertex3_mem rev132_vertex0_mem (by decide)
def rev132_s1_lr : FractionPoint := ⟨1,2,1,2⟩
theorem rev132_s1_lr_mem : rev132_s1_lr.real ∈ rationalHull (fractionRow132.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow132 rev132_plane73 rev132_vertex3 rev132_vertex0 rev132_s1_lr
    rev132_vertex3_mem rev132_vertex0_mem (by decide)
def rev132_s1_ul : FractionPoint := ⟨857155134382729,1901166327250000,403436064050273,760466530900000⟩
theorem rev132_s1_ul_mem : rev132_s1_ul.real ∈ rationalHull (fractionRow132.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow132 rev132_plane53 rev132_vertex1 rev132_vertex0 rev132_s1_ul
    rev132_vertex1_mem rev132_vertex0_mem (by decide)
def rev132_s1_ur : FractionPoint := ⟨1,2,1,2⟩
theorem rev132_s1_ur_mem : rev132_s1_ur.real ∈ rationalHull (fractionRow132.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow132 rev132_plane53 rev132_vertex1 rev132_vertex0 rev132_s1_ur
    rev132_vertex1_mem rev132_vertex0_mem (by decide)
theorem rev132_slab1 (p : Point) (hp : p∈IntegerCarrier rev132_planes)
    (hx0 : rev132_s1_ll.real.1≤p.1) (hx1 : p.1≤rev132_s1_lr.real.1) :
    p∈rationalHull (fractionRow132.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev132_plane73 rev132_plane53 rev132_s1_ll rev132_s1_lr rev132_s1_ul rev132_s1_ur
    (by decide) rev132_s1_ll_mem rev132_s1_lr_mem rev132_s1_ul_mem rev132_s1_ur_mem p
    (hp _ rev132_plane73_mem) (hp _ rev132_plane53_mem) hx0 hx1
theorem rev132_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev132_planes) : rev132_s0_ll.real.1≤p.1 := by
  have hc := rev132_plane49.combine_sound rev132_plane69 2112812000000 2112812000000 (by decide) (by decide) p
    (hp _ rev132_plane49_mem) (hp _ rev132_plane69_mem)
  exact (rev132_plane49.combine rev132_plane69 2112812000000 2112812000000).xBoundCheck_sound rev132_s0_ll.nx rev132_s0_ll.dx true (by decide) p hc
theorem rev132_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev132_planes) : p.1≤rev132_s1_lr.real.1 := by
  have hc := rev132_plane10.combine_sound rev132_plane33 1343640000000 1343640000000 (by decide) (by decide) p
    (hp _ rev132_plane10_mem) (hp _ rev132_plane33_mem)
  exact (rev132_plane10.combine rev132_plane33 1343640000000 1343640000000).xBoundCheck_sound rev132_s1_lr.nx rev132_s1_lr.dx false (by decide) p hc
theorem rev132_hull (p : Point) (hp : p∈IntegerCarrier rev132_planes) :
    p∈rationalHull (fractionRow132.map FractionPoint.rational) := by
  have hxlo := rev132_bound0_lo p hp
  have hxhi := rev132_bound0_hi p hp
  by_cases h0 : p.1≤rev132_s0_lr.real.1
  · exact rev132_slab0 p hp hxlo h0
  exact rev132_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull132 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,6,6,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow132 := by
  rw [← fractionRow132_correct]
  exact rev132_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull132
