import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks25
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev207_planes : List IntegerPlane := integerOverlayPlanes ![14,14,8,11]
def rev207_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev207_plane3_mem : rev207_plane3 ∈ rev207_planes := by decide
def rev207_plane37 : IntegerPlane := ⟨2083356000000,(-746024000000),371492707941⟩
theorem rev207_plane37_mem : rev207_plane37 ∈ rev207_planes := by decide
def rev207_plane48 : IntegerPlane := ⟨(-2112760000000),48252000000,(-1081757250915)⟩
theorem rev207_plane48_mem : rev207_plane48 ∈ rev207_planes := by decide
def rev207_vertex0 : FractionPoint := fractionRow207[0]!
theorem rev207_vertex0_mem : rev207_vertex0∈fractionRow207 := by decide
def rev207_vertex1 : FractionPoint := fractionRow207[1]!
theorem rev207_vertex1_mem : rev207_vertex1∈fractionRow207 := by decide
def rev207_vertex2 : FractionPoint := fractionRow207[2]!
theorem rev207_vertex2_mem : rev207_vertex2∈fractionRow207 := by decide
def rev207_s0_ll : FractionPoint := ⟨197272901303260707,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev207_s0_ll_mem : rev207_s0_ll.real ∈ rationalHull (fractionRow207.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow207 rev207_plane37 rev207_vertex2 rev207_vertex0 rev207_s0_ll
    rev207_vertex2_mem rev207_vertex0_mem (by decide)
def rev207_s0_lr : FractionPoint := ⟨226001850183,422552000000,78466830965992179,78808483312000000⟩
theorem rev207_s0_lr_mem : rev207_s0_lr.real ∈ rationalHull (fractionRow207.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow207 rev207_plane37 rev207_vertex2 rev207_vertex0 rev207_s0_lr
    rev207_vertex2_mem rev207_vertex0_mem (by decide)
def rev207_s0_ul : FractionPoint := ⟨197272901303260707,368910893132000000,73440526280392179,73782178626400000⟩
theorem rev207_s0_ul_mem : rev207_s0_ul.real ∈ rationalHull (fractionRow207.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow207 rev207_plane48 rev207_vertex2 rev207_vertex1 rev207_s0_ul
    rev207_vertex2_mem rev207_vertex1_mem (by decide)
def rev207_s0_ur : FractionPoint := ⟨226001850183,422552000000,1,1⟩
theorem rev207_s0_ur_mem : rev207_s0_ur.real ∈ rationalHull (fractionRow207.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow207 rev207_plane48 rev207_vertex2 rev207_vertex1 rev207_s0_ur
    rev207_vertex2_mem rev207_vertex1_mem (by decide)
theorem rev207_slab0 (p : Point) (hp : p∈IntegerCarrier rev207_planes)
    (hx0 : rev207_s0_ll.real.1≤p.1) (hx1 : p.1≤rev207_s0_lr.real.1) :
    p∈rationalHull (fractionRow207.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev207_plane37 rev207_plane48 rev207_s0_ll rev207_s0_lr rev207_s0_ul rev207_s0_ur
    (by decide) rev207_s0_ll_mem rev207_s0_lr_mem rev207_s0_ul_mem rev207_s0_ur_mem p
    (hp _ rev207_plane37_mem) (hp _ rev207_plane48_mem) hx0 hx1
def rev207_s1_ll : FractionPoint := ⟨226001850183,422552000000,78466830965992179,78808483312000000⟩
theorem rev207_s1_ll_mem : rev207_s1_ll.real ∈ rationalHull (fractionRow207.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow207 rev207_plane37 rev207_vertex2 rev207_vertex0 rev207_s1_ll
    rev207_vertex2_mem rev207_vertex0_mem (by decide)
def rev207_s1_lr : FractionPoint := ⟨1117516707941,2083356000000,1,1⟩
theorem rev207_s1_lr_mem : rev207_s1_lr.real ∈ rationalHull (fractionRow207.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow207 rev207_plane37 rev207_vertex2 rev207_vertex0 rev207_s1_lr
    rev207_vertex2_mem rev207_vertex0_mem (by decide)
def rev207_s1_ul : FractionPoint := ⟨226001850183,422552000000,1,1⟩
theorem rev207_s1_ul_mem : rev207_s1_ul.real ∈ rationalHull (fractionRow207.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow207 rev207_plane3 rev207_vertex1 rev207_vertex0 rev207_s1_ul
    rev207_vertex1_mem rev207_vertex0_mem (by decide)
def rev207_s1_ur : FractionPoint := ⟨1117516707941,2083356000000,1,1⟩
theorem rev207_s1_ur_mem : rev207_s1_ur.real ∈ rationalHull (fractionRow207.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow207 rev207_plane3 rev207_vertex1 rev207_vertex0 rev207_s1_ur
    rev207_vertex1_mem rev207_vertex0_mem (by decide)
theorem rev207_slab1 (p : Point) (hp : p∈IntegerCarrier rev207_planes)
    (hx0 : rev207_s1_ll.real.1≤p.1) (hx1 : p.1≤rev207_s1_lr.real.1) :
    p∈rationalHull (fractionRow207.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev207_plane37 rev207_plane3 rev207_s1_ll rev207_s1_lr rev207_s1_ul rev207_s1_ur
    (by decide) rev207_s1_ll_mem rev207_s1_lr_mem rev207_s1_ul_mem rev207_s1_ur_mem p
    (hp _ rev207_plane37_mem) (hp _ rev207_plane3_mem) hx0 hx1
theorem rev207_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev207_planes) : rev207_s0_ll.real.1≤p.1 := by
  have hc := rev207_plane37.combine_sound rev207_plane48 48252000000 746024000000 (by decide) (by decide) p
    (hp _ rev207_plane37_mem) (hp _ rev207_plane48_mem)
  exact (rev207_plane37.combine rev207_plane48 48252000000 746024000000).xBoundCheck_sound rev207_s0_ll.nx rev207_s0_ll.dx true (by decide) p hc
theorem rev207_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev207_planes) : p.1≤rev207_s1_lr.real.1 := by
  have hc := rev207_plane3.combine_sound rev207_plane37 746024000000 1 (by decide) (by decide) p
    (hp _ rev207_plane3_mem) (hp _ rev207_plane37_mem)
  exact (rev207_plane3.combine rev207_plane37 746024000000 1).xBoundCheck_sound rev207_s1_lr.nx rev207_s1_lr.dx false (by decide) p hc
theorem rev207_hull (p : Point) (hp : p∈IntegerCarrier rev207_planes) :
    p∈rationalHull (fractionRow207.map FractionPoint.rational) := by
  have hxlo := rev207_bound0_lo p hp
  have hxhi := rev207_bound0_hi p hp
  by_cases h0 : p.1≤rev207_s0_lr.real.1
  · exact rev207_slab0 p hp hxlo h0
  exact rev207_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull207 (p : Point)
    (hp : ∀ g, ClosedCell ((![14,14,8,11] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow207 := by
  rw [← fractionRow207_correct]
  exact rev207_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull207
