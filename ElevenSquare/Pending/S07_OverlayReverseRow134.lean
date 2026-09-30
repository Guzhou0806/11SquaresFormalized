import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks16
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev134_planes : List IntegerPlane := integerOverlayPlanes ![9,6,9,6]
def rev134_plane10 : IntegerPlane := ⟨2164112000000,(-1343640000000),410236000000⟩
theorem rev134_plane10_mem : rev134_plane10 ∈ rev134_planes := by decide
def rev134_plane33 : IntegerPlane := ⟨2164112000000,1343640000000,1753876000000⟩
theorem rev134_plane33_mem : rev134_plane33 ∈ rev134_planes := by decide
def rev134_plane34 : IntegerPlane := ⟨51300000000,2168356000000,1214821164456⟩
theorem rev134_plane34_mem : rev134_plane34 ∈ rev134_planes := by decide
def rev134_plane49 : IntegerPlane := ⟨(-2168356000000),(-51300000000),(-1004834835544)⟩
theorem rev134_plane49_mem : rev134_plane49 ∈ rev134_planes := by decide
def rev134_plane50 : IntegerPlane := ⟨(-1343640000000),(-2164112000000),(-1753876000000)⟩
theorem rev134_plane50_mem : rev134_plane50 ∈ rev134_planes := by decide
def rev134_vertex0 : FractionPoint := fractionRow134[0]!
theorem rev134_vertex0_mem : rev134_vertex0∈fractionRow134 := by decide
def rev134_vertex1 : FractionPoint := fractionRow134[1]!
theorem rev134_vertex1_mem : rev134_vertex1∈fractionRow134 := by decide
def rev134_vertex2 : FractionPoint := fractionRow134[2]!
theorem rev134_vertex2_mem : rev134_vertex2∈fractionRow134 := by decide
def rev134_vertex3 : FractionPoint := fractionRow134[3]!
theorem rev134_vertex3_mem : rev134_vertex3∈fractionRow134 := by decide
def rev134_s0_ll : FractionPoint := ⟨6273255497,13928000000,7654744503,13928000000⟩
theorem rev134_s0_ll_mem : rev134_s0_ll.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane49 rev134_vertex2 rev134_vertex3 rev134_s0_ll
    rev134_vertex2_mem rev134_vertex3_mem (by decide)
def rev134_s0_lr : FractionPoint := ⟨857155134382729,1901166327250000,403436064050273,760466530900000⟩
theorem rev134_s0_lr_mem : rev134_s0_lr.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane49 rev134_vertex2 rev134_vertex3 rev134_s0_lr
    rev134_vertex2_mem rev134_vertex3_mem (by decide)
def rev134_s0_ul : FractionPoint := ⟨6273255497,13928000000,7654744503,13928000000⟩
theorem rev134_s0_ul_mem : rev134_s0_ul.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane34 rev134_vertex2 rev134_vertex1 rev134_s0_ul
    rev134_vertex2_mem rev134_vertex1_mem (by decide)
def rev134_s0_ur : FractionPoint := ⟨857155134382729,1901166327250000,59621185081593362277,108484352965539500000⟩
theorem rev134_s0_ur_mem : rev134_s0_ur.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane34 rev134_vertex2 rev134_vertex1 rev134_s0_ur
    rev134_vertex2_mem rev134_vertex1_mem (by decide)
theorem rev134_slab0 (p : Point) (hp : p∈IntegerCarrier rev134_planes)
    (hx0 : rev134_s0_ll.real.1≤p.1) (hx1 : p.1≤rev134_s0_lr.real.1) :
    p∈rationalHull (fractionRow134.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev134_plane49 rev134_plane34 rev134_s0_ll rev134_s0_lr rev134_s0_ul rev134_s0_ur
    (by decide) rev134_s0_ll_mem rev134_s0_lr_mem rev134_s0_ul_mem rev134_s0_ur_mem p
    (hp _ rev134_plane49_mem) (hp _ rev134_plane34_mem) hx0 hx1
def rev134_s1_ll : FractionPoint := ⟨857155134382729,1901166327250000,403436064050273,760466530900000⟩
theorem rev134_s1_ll_mem : rev134_s1_ll.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane50 rev134_vertex3 rev134_vertex0 rev134_s1_ll
    rev134_vertex3_mem rev134_vertex0_mem (by decide)
def rev134_s1_lr : FractionPoint := ⟨357030466849727,760466530900000,21351089521770030343,41143368627976520000⟩
theorem rev134_s1_lr_mem : rev134_s1_lr.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane50 rev134_vertex3 rev134_vertex0 rev134_s1_lr
    rev134_vertex3_mem rev134_vertex0_mem (by decide)
def rev134_s1_ul : FractionPoint := ⟨857155134382729,1901166327250000,59621185081593362277,108484352965539500000⟩
theorem rev134_s1_ul_mem : rev134_s1_ul.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane34 rev134_vertex2 rev134_vertex1 rev134_s1_ul
    rev134_vertex2_mem rev134_vertex1_mem (by decide)
def rev134_s1_ur : FractionPoint := ⟨357030466849727,760466530900000,1044011192867271,1901166327250000⟩
theorem rev134_s1_ur_mem : rev134_s1_ur.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane34 rev134_vertex2 rev134_vertex1 rev134_s1_ur
    rev134_vertex2_mem rev134_vertex1_mem (by decide)
theorem rev134_slab1 (p : Point) (hp : p∈IntegerCarrier rev134_planes)
    (hx0 : rev134_s1_ll.real.1≤p.1) (hx1 : p.1≤rev134_s1_lr.real.1) :
    p∈rationalHull (fractionRow134.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev134_plane50 rev134_plane34 rev134_s1_ll rev134_s1_lr rev134_s1_ul rev134_s1_ur
    (by decide) rev134_s1_ll_mem rev134_s1_lr_mem rev134_s1_ul_mem rev134_s1_ur_mem p
    (hp _ rev134_plane50_mem) (hp _ rev134_plane34_mem) hx0 hx1
def rev134_s2_ll : FractionPoint := ⟨357030466849727,760466530900000,21351089521770030343,41143368627976520000⟩
theorem rev134_s2_ll_mem : rev134_s2_ll.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane50 rev134_vertex3 rev134_vertex0 rev134_s2_ll
    rev134_vertex3_mem rev134_vertex0_mem (by decide)
def rev134_s2_lr : FractionPoint := ⟨1,2,1,2⟩
theorem rev134_s2_lr_mem : rev134_s2_lr.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane50 rev134_vertex3 rev134_vertex0 rev134_s2_lr
    rev134_vertex3_mem rev134_vertex0_mem (by decide)
def rev134_s2_ul : FractionPoint := ⟨357030466849727,760466530900000,1044011192867271,1901166327250000⟩
theorem rev134_s2_ul_mem : rev134_s2_ul.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane33 rev134_vertex1 rev134_vertex0 rev134_s2_ul
    rev134_vertex1_mem rev134_vertex0_mem (by decide)
def rev134_s2_ur : FractionPoint := ⟨1,2,1,2⟩
theorem rev134_s2_ur_mem : rev134_s2_ur.real ∈ rationalHull (fractionRow134.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow134 rev134_plane33 rev134_vertex1 rev134_vertex0 rev134_s2_ur
    rev134_vertex1_mem rev134_vertex0_mem (by decide)
theorem rev134_slab2 (p : Point) (hp : p∈IntegerCarrier rev134_planes)
    (hx0 : rev134_s2_ll.real.1≤p.1) (hx1 : p.1≤rev134_s2_lr.real.1) :
    p∈rationalHull (fractionRow134.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev134_plane50 rev134_plane33 rev134_s2_ll rev134_s2_lr rev134_s2_ul rev134_s2_ur
    (by decide) rev134_s2_ll_mem rev134_s2_lr_mem rev134_s2_ul_mem rev134_s2_ur_mem p
    (hp _ rev134_plane50_mem) (hp _ rev134_plane33_mem) hx0 hx1
theorem rev134_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev134_planes) : rev134_s0_ll.real.1≤p.1 := by
  have hc := rev134_plane34.combine_sound rev134_plane49 51300000000 2168356000000 (by decide) (by decide) p
    (hp _ rev134_plane34_mem) (hp _ rev134_plane49_mem)
  exact (rev134_plane34.combine rev134_plane49 51300000000 2168356000000).xBoundCheck_sound rev134_s0_ll.nx rev134_s0_ll.dx true (by decide) p hc
theorem rev134_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev134_planes) : p.1≤rev134_s2_lr.real.1 := by
  have hc := rev134_plane10.combine_sound rev134_plane33 1343640000000 1343640000000 (by decide) (by decide) p
    (hp _ rev134_plane10_mem) (hp _ rev134_plane33_mem)
  exact (rev134_plane10.combine rev134_plane33 1343640000000 1343640000000).xBoundCheck_sound rev134_s2_lr.nx rev134_s2_lr.dx false (by decide) p hc
theorem rev134_hull (p : Point) (hp : p∈IntegerCarrier rev134_planes) :
    p∈rationalHull (fractionRow134.map FractionPoint.rational) := by
  have hxlo := rev134_bound0_lo p hp
  have hxhi := rev134_bound0_hi p hp
  by_cases h0 : p.1≤rev134_s0_lr.real.1
  · exact rev134_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev134_s1_lr.real.1
  · exact rev134_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev134_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull134 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,6,9,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow134 := by
  rw [← fractionRow134_correct]
  exact rev134_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull134
