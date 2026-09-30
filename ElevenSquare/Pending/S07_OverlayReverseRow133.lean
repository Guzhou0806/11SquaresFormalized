import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks16
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev133_planes : List IntegerPlane := integerOverlayPlanes ![9,6,6,9]
def rev133_plane9 : IntegerPlane := ⟨51300000000,(-2168356000000),(-953534835544)⟩
theorem rev133_plane9_mem : rev133_plane9 ∈ rev133_planes := by decide
def rev133_plane10 : IntegerPlane := ⟨2164112000000,(-1343640000000),410236000000⟩
theorem rev133_plane10_mem : rev133_plane10 ∈ rev133_planes := by decide
def rev133_plane33 : IntegerPlane := ⟨2164112000000,1343640000000,1753876000000⟩
theorem rev133_plane33_mem : rev133_plane33 ∈ rev133_planes := by decide
def rev133_plane69 : IntegerPlane := ⟨(-2168356000000),51300000000,(-953534835544)⟩
theorem rev133_plane69_mem : rev133_plane69 ∈ rev133_planes := by decide
def rev133_plane70 : IntegerPlane := ⟨(-1343640000000),2164112000000,410236000000⟩
theorem rev133_plane70_mem : rev133_plane70 ∈ rev133_planes := by decide
def rev133_vertex0 : FractionPoint := fractionRow133[0]!
theorem rev133_vertex0_mem : rev133_vertex0∈fractionRow133 := by decide
def rev133_vertex1 : FractionPoint := fractionRow133[1]!
theorem rev133_vertex1_mem : rev133_vertex1∈fractionRow133 := by decide
def rev133_vertex2 : FractionPoint := fractionRow133[2]!
theorem rev133_vertex2_mem : rev133_vertex2∈fractionRow133 := by decide
def rev133_vertex3 : FractionPoint := fractionRow133[3]!
theorem rev133_vertex3_mem : rev133_vertex3∈fractionRow133 := by decide
def rev133_s0_ll : FractionPoint := ⟨6273255497,13928000000,6273255497,13928000000⟩
theorem rev133_s0_ll_mem : rev133_s0_ll.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane9 rev133_vertex0 rev133_vertex1 rev133_s0_ll
    rev133_vertex0_mem rev133_vertex1_mem (by decide)
def rev133_s0_lr : FractionPoint := ⟨857155134382729,1901166327250000,48863167883946137723,108484352965539500000⟩
theorem rev133_s0_lr_mem : rev133_s0_lr.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane9 rev133_vertex0 rev133_vertex1 rev133_s0_lr
    rev133_vertex0_mem rev133_vertex1_mem (by decide)
def rev133_s0_ul : FractionPoint := ⟨6273255497,13928000000,6273255497,13928000000⟩
theorem rev133_s0_ul_mem : rev133_s0_ul.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane69 rev133_vertex0 rev133_vertex3 rev133_s0_ul
    rev133_vertex0_mem rev133_vertex3_mem (by decide)
def rev133_s0_ur : FractionPoint := ⟨857155134382729,1901166327250000,357030466849727,760466530900000⟩
theorem rev133_s0_ur_mem : rev133_s0_ur.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane69 rev133_vertex0 rev133_vertex3 rev133_s0_ur
    rev133_vertex0_mem rev133_vertex3_mem (by decide)
theorem rev133_slab0 (p : Point) (hp : p∈IntegerCarrier rev133_planes)
    (hx0 : rev133_s0_ll.real.1≤p.1) (hx1 : p.1≤rev133_s0_lr.real.1) :
    p∈rationalHull (fractionRow133.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev133_plane9 rev133_plane69 rev133_s0_ll rev133_s0_lr rev133_s0_ul rev133_s0_ur
    (by decide) rev133_s0_ll_mem rev133_s0_lr_mem rev133_s0_ul_mem rev133_s0_ur_mem p
    (hp _ rev133_plane9_mem) (hp _ rev133_plane69_mem) hx0 hx1
def rev133_s1_ll : FractionPoint := ⟨857155134382729,1901166327250000,48863167883946137723,108484352965539500000⟩
theorem rev133_s1_ll_mem : rev133_s1_ll.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane9 rev133_vertex0 rev133_vertex1 rev133_s1_ll
    rev133_vertex0_mem rev133_vertex1_mem (by decide)
def rev133_s1_lr : FractionPoint := ⟨357030466849727,760466530900000,857155134382729,1901166327250000⟩
theorem rev133_s1_lr_mem : rev133_s1_lr.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane9 rev133_vertex0 rev133_vertex1 rev133_s1_lr
    rev133_vertex0_mem rev133_vertex1_mem (by decide)
def rev133_s1_ul : FractionPoint := ⟨857155134382729,1901166327250000,357030466849727,760466530900000⟩
theorem rev133_s1_ul_mem : rev133_s1_ul.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane70 rev133_vertex3 rev133_vertex2 rev133_s1_ul
    rev133_vertex3_mem rev133_vertex2_mem (by decide)
def rev133_s1_ur : FractionPoint := ⟨357030466849727,760466530900000,19792279106206489657,41143368627976520000⟩
theorem rev133_s1_ur_mem : rev133_s1_ur.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane70 rev133_vertex3 rev133_vertex2 rev133_s1_ur
    rev133_vertex3_mem rev133_vertex2_mem (by decide)
theorem rev133_slab1 (p : Point) (hp : p∈IntegerCarrier rev133_planes)
    (hx0 : rev133_s1_ll.real.1≤p.1) (hx1 : p.1≤rev133_s1_lr.real.1) :
    p∈rationalHull (fractionRow133.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev133_plane9 rev133_plane70 rev133_s1_ll rev133_s1_lr rev133_s1_ul rev133_s1_ur
    (by decide) rev133_s1_ll_mem rev133_s1_lr_mem rev133_s1_ul_mem rev133_s1_ur_mem p
    (hp _ rev133_plane9_mem) (hp _ rev133_plane70_mem) hx0 hx1
def rev133_s2_ll : FractionPoint := ⟨357030466849727,760466530900000,857155134382729,1901166327250000⟩
theorem rev133_s2_ll_mem : rev133_s2_ll.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane10 rev133_vertex1 rev133_vertex2 rev133_s2_ll
    rev133_vertex1_mem rev133_vertex2_mem (by decide)
def rev133_s2_lr : FractionPoint := ⟨1,2,1,2⟩
theorem rev133_s2_lr_mem : rev133_s2_lr.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane10 rev133_vertex1 rev133_vertex2 rev133_s2_lr
    rev133_vertex1_mem rev133_vertex2_mem (by decide)
def rev133_s2_ul : FractionPoint := ⟨357030466849727,760466530900000,19792279106206489657,41143368627976520000⟩
theorem rev133_s2_ul_mem : rev133_s2_ul.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane70 rev133_vertex3 rev133_vertex2 rev133_s2_ul
    rev133_vertex3_mem rev133_vertex2_mem (by decide)
def rev133_s2_ur : FractionPoint := ⟨1,2,1,2⟩
theorem rev133_s2_ur_mem : rev133_s2_ur.real ∈ rationalHull (fractionRow133.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow133 rev133_plane70 rev133_vertex3 rev133_vertex2 rev133_s2_ur
    rev133_vertex3_mem rev133_vertex2_mem (by decide)
theorem rev133_slab2 (p : Point) (hp : p∈IntegerCarrier rev133_planes)
    (hx0 : rev133_s2_ll.real.1≤p.1) (hx1 : p.1≤rev133_s2_lr.real.1) :
    p∈rationalHull (fractionRow133.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev133_plane10 rev133_plane70 rev133_s2_ll rev133_s2_lr rev133_s2_ul rev133_s2_ur
    (by decide) rev133_s2_ll_mem rev133_s2_lr_mem rev133_s2_ul_mem rev133_s2_ur_mem p
    (hp _ rev133_plane10_mem) (hp _ rev133_plane70_mem) hx0 hx1
theorem rev133_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev133_planes) : rev133_s0_ll.real.1≤p.1 := by
  have hc := rev133_plane9.combine_sound rev133_plane69 51300000000 2168356000000 (by decide) (by decide) p
    (hp _ rev133_plane9_mem) (hp _ rev133_plane69_mem)
  exact (rev133_plane9.combine rev133_plane69 51300000000 2168356000000).xBoundCheck_sound rev133_s0_ll.nx rev133_s0_ll.dx true (by decide) p hc
theorem rev133_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev133_planes) : p.1≤rev133_s2_lr.real.1 := by
  have hc := rev133_plane10.combine_sound rev133_plane33 1343640000000 1343640000000 (by decide) (by decide) p
    (hp _ rev133_plane10_mem) (hp _ rev133_plane33_mem)
  exact (rev133_plane10.combine rev133_plane33 1343640000000 1343640000000).xBoundCheck_sound rev133_s2_lr.nx rev133_s2_lr.dx false (by decide) p hc
theorem rev133_hull (p : Point) (hp : p∈IntegerCarrier rev133_planes) :
    p∈rationalHull (fractionRow133.map FractionPoint.rational) := by
  have hxlo := rev133_bound0_lo p hp
  have hxhi := rev133_bound0_hi p hp
  by_cases h0 : p.1≤rev133_s0_lr.real.1
  · exact rev133_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev133_s1_lr.real.1
  · exact rev133_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev133_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull133 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,6,6,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow133 := by
  rw [← fractionRow133_correct]
  exact rev133_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull133
