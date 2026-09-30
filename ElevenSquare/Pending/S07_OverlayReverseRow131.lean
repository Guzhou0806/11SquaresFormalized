import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks16
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev131_planes : List IntegerPlane := integerOverlayPlanes ![9,6,6,5]
def rev131_plane9 : IntegerPlane := ⟨51300000000,(-2168356000000),(-953534835544)⟩
theorem rev131_plane9_mem : rev131_plane9 ∈ rev131_planes := by decide
def rev131_plane46 : IntegerPlane := ⟨(-2218132000000),13084000000,(-610502975028)⟩
theorem rev131_plane46_mem : rev131_plane46 ∈ rev131_planes := by decide
def rev131_plane49 : IntegerPlane := ⟨(-824716000000),2112812000000,749041164456⟩
theorem rev131_plane49_mem : rev131_plane49 ∈ rev131_planes := by decide
def rev131_plane70 : IntegerPlane := ⟨824716000000,2112812000000,1363770835544⟩
theorem rev131_plane70_mem : rev131_plane70 ∈ rev131_planes := by decide
def rev131_plane73 : IntegerPlane := ⟨2168356000000,(-51300000000),953534835544⟩
theorem rev131_plane73_mem : rev131_plane73 ∈ rev131_planes := by decide
def rev131_vertex0 : FractionPoint := fractionRow131[0]!
theorem rev131_vertex0_mem : rev131_vertex0∈fractionRow131 := by decide
def rev131_vertex1 : FractionPoint := fractionRow131[1]!
theorem rev131_vertex1_mem : rev131_vertex1∈fractionRow131 := by decide
def rev131_vertex2 : FractionPoint := fractionRow131[2]!
theorem rev131_vertex2_mem : rev131_vertex2∈fractionRow131 := by decide
def rev131_vertex3 : FractionPoint := fractionRow131[3]!
theorem rev131_vertex3_mem : rev131_vertex3∈fractionRow131 := by decide
def rev131_vertex4 : FractionPoint := fractionRow131[4]!
theorem rev131_vertex4_mem : rev131_vertex4∈fractionRow131 := by decide
def rev131_s0_ll : FractionPoint := ⟨4395604732592341,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev131_s0_ll_mem : rev131_s0_ll.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane9 rev131_vertex0 rev131_vertex1 rev131_s0_ll
    rev131_vertex0_mem rev131_vertex1_mem (by decide)
def rev131_s0_lr : FractionPoint := ⟨16245980828382513,58446316538000000,744263390061979215047,1667531857145678000000⟩
theorem rev131_s0_lr_mem : rev131_s0_lr.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane9 rev131_vertex0 rev131_vertex1 rev131_s0_lr
    rev131_vertex0_mem rev131_vertex1_mem (by decide)
def rev131_s0_ul : FractionPoint := ⟨4395604732592341,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev131_s0_ul_mem : rev131_s0_ul.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane46 rev131_vertex0 rev131_vertex4 rev131_s0_ul
    rev131_vertex0_mem rev131_vertex4_mem (by decide)
def rev131_s0_ur : FractionPoint := ⟨16245980828382513,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev131_s0_ur_mem : rev131_s0_ur.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane46 rev131_vertex0 rev131_vertex4 rev131_s0_ur
    rev131_vertex0_mem rev131_vertex4_mem (by decide)
theorem rev131_slab0 (p : Point) (hp : p∈IntegerCarrier rev131_planes)
    (hx0 : rev131_s0_ll.real.1≤p.1) (hx1 : p.1≤rev131_s0_lr.real.1) :
    p∈rationalHull (fractionRow131.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev131_plane9 rev131_plane46 rev131_s0_ll rev131_s0_lr rev131_s0_ul rev131_s0_ur
    (by decide) rev131_s0_ll_mem rev131_s0_lr_mem rev131_s0_ul_mem rev131_s0_ur_mem p
    (hp _ rev131_plane9_mem) (hp _ rev131_plane46_mem) hx0 hx1
def rev131_s1_ll : FractionPoint := ⟨16245980828382513,58446316538000000,744263390061979215047,1667531857145678000000⟩
theorem rev131_s1_ll_mem : rev131_s1_ll.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane9 rev131_vertex0 rev131_vertex1 rev131_s1_ll
    rev131_vertex0_mem rev131_vertex1_mem (by decide)
def rev131_s1_lr : FractionPoint := ⟨38420604443,103089500000,329836863278747,735311631125000⟩
theorem rev131_s1_lr_mem : rev131_s1_lr.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane9 rev131_vertex0 rev131_vertex1 rev131_s1_lr
    rev131_vertex0_mem rev131_vertex1_mem (by decide)
def rev131_s1_ul : FractionPoint := ⟨16245980828382513,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev131_s1_ul_mem : rev131_s1_ul.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane49 rev131_vertex4 rev131_vertex3 rev131_s1_ul
    rev131_vertex4_mem rev131_vertex3_mem (by decide)
def rev131_s1_ur : FractionPoint := ⟨38420604443,103089500000,1,2⟩
theorem rev131_s1_ur_mem : rev131_s1_ur.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane49 rev131_vertex4 rev131_vertex3 rev131_s1_ur
    rev131_vertex4_mem rev131_vertex3_mem (by decide)
theorem rev131_slab1 (p : Point) (hp : p∈IntegerCarrier rev131_planes)
    (hx0 : rev131_s1_ll.real.1≤p.1) (hx1 : p.1≤rev131_s1_lr.real.1) :
    p∈rationalHull (fractionRow131.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev131_plane9 rev131_plane49 rev131_s1_ll rev131_s1_lr rev131_s1_ul rev131_s1_ur
    (by decide) rev131_s1_ll_mem rev131_s1_lr_mem rev131_s1_ul_mem rev131_s1_ur_mem p
    (hp _ rev131_plane9_mem) (hp _ rev131_plane49_mem) hx0 hx1
def rev131_s2_ll : FractionPoint := ⟨38420604443,103089500000,329836863278747,735311631125000⟩
theorem rev131_s2_ll_mem : rev131_s2_ll.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane9 rev131_vertex0 rev131_vertex1 rev131_s2_ll
    rev131_vertex0_mem rev131_vertex1_mem (by decide)
def rev131_s2_lr : FractionPoint := ⟨6273255497,13928000000,6273255497,13928000000⟩
theorem rev131_s2_lr_mem : rev131_s2_lr.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane9 rev131_vertex0 rev131_vertex1 rev131_s2_lr
    rev131_vertex0_mem rev131_vertex1_mem (by decide)
def rev131_s2_ul : FractionPoint := ⟨38420604443,103089500000,1,2⟩
theorem rev131_s2_ul_mem : rev131_s2_ul.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane70 rev131_vertex3 rev131_vertex2 rev131_s2_ul
    rev131_vertex3_mem rev131_vertex2_mem (by decide)
def rev131_s2_ur : FractionPoint := ⟨6273255497,13928000000,691047300849649,1471362276800000⟩
theorem rev131_s2_ur_mem : rev131_s2_ur.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane70 rev131_vertex3 rev131_vertex2 rev131_s2_ur
    rev131_vertex3_mem rev131_vertex2_mem (by decide)
theorem rev131_slab2 (p : Point) (hp : p∈IntegerCarrier rev131_planes)
    (hx0 : rev131_s2_ll.real.1≤p.1) (hx1 : p.1≤rev131_s2_lr.real.1) :
    p∈rationalHull (fractionRow131.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev131_plane9 rev131_plane70 rev131_s2_ll rev131_s2_lr rev131_s2_ul rev131_s2_ur
    (by decide) rev131_s2_ll_mem rev131_s2_lr_mem rev131_s2_ul_mem rev131_s2_ur_mem p
    (hp _ rev131_plane9_mem) (hp _ rev131_plane70_mem) hx0 hx1
def rev131_s3_ll : FractionPoint := ⟨6273255497,13928000000,6273255497,13928000000⟩
theorem rev131_s3_ll_mem : rev131_s3_ll.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane73 rev131_vertex1 rev131_vertex2 rev131_s3_ll
    rev131_vertex1_mem rev131_vertex2_mem (by decide)
def rev131_s3_lr : FractionPoint := ⟨857155134382729,1901166327250000,357030466849727,760466530900000⟩
theorem rev131_s3_lr_mem : rev131_s3_lr.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane73 rev131_vertex1 rev131_vertex2 rev131_s3_lr
    rev131_vertex1_mem rev131_vertex2_mem (by decide)
def rev131_s3_ul : FractionPoint := ⟨6273255497,13928000000,691047300849649,1471362276800000⟩
theorem rev131_s3_ul_mem : rev131_s3_ul.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane70 rev131_vertex3 rev131_vertex2 rev131_s3_ul
    rev131_vertex3_mem rev131_vertex2_mem (by decide)
def rev131_s3_ur : FractionPoint := ⟨857155134382729,1901166327250000,357030466849727,760466530900000⟩
theorem rev131_s3_ur_mem : rev131_s3_ur.real ∈ rationalHull (fractionRow131.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow131 rev131_plane70 rev131_vertex3 rev131_vertex2 rev131_s3_ur
    rev131_vertex3_mem rev131_vertex2_mem (by decide)
theorem rev131_slab3 (p : Point) (hp : p∈IntegerCarrier rev131_planes)
    (hx0 : rev131_s3_ll.real.1≤p.1) (hx1 : p.1≤rev131_s3_lr.real.1) :
    p∈rationalHull (fractionRow131.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev131_plane73 rev131_plane70 rev131_s3_ll rev131_s3_lr rev131_s3_ul rev131_s3_ur
    (by decide) rev131_s3_ll_mem rev131_s3_lr_mem rev131_s3_ul_mem rev131_s3_ur_mem p
    (hp _ rev131_plane73_mem) (hp _ rev131_plane70_mem) hx0 hx1
theorem rev131_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev131_planes) : rev131_s0_ll.real.1≤p.1 := by
  have hc := rev131_plane9.combine_sound rev131_plane46 13084000000 2168356000000 (by decide) (by decide) p
    (hp _ rev131_plane9_mem) (hp _ rev131_plane46_mem)
  exact (rev131_plane9.combine rev131_plane46 13084000000 2168356000000).xBoundCheck_sound rev131_s0_ll.nx rev131_s0_ll.dx true (by decide) p hc
theorem rev131_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev131_planes) : p.1≤rev131_s3_lr.real.1 := by
  have hc := rev131_plane70.combine_sound rev131_plane73 51300000000 2112812000000 (by decide) (by decide) p
    (hp _ rev131_plane70_mem) (hp _ rev131_plane73_mem)
  exact (rev131_plane70.combine rev131_plane73 51300000000 2112812000000).xBoundCheck_sound rev131_s3_lr.nx rev131_s3_lr.dx false (by decide) p hc
theorem rev131_hull (p : Point) (hp : p∈IntegerCarrier rev131_planes) :
    p∈rationalHull (fractionRow131.map FractionPoint.rational) := by
  have hxlo := rev131_bound0_lo p hp
  have hxhi := rev131_bound0_hi p hp
  by_cases h0 : p.1≤rev131_s0_lr.real.1
  · exact rev131_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev131_s1_lr.real.1
  · exact rev131_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev131_s2_lr.real.1
  · exact rev131_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev131_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull131 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,6,6,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow131 := by
  rw [← fractionRow131_correct]
  exact rev131_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull131
