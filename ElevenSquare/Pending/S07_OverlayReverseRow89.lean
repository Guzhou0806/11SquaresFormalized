import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks11
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev89_planes : List IntegerPlane := integerOverlayPlanes ![6,9,10,9]
def rev89_plane29 : IntegerPlane := ⟨(-51300000000),(-2168356000000),(-1004834835544)⟩
theorem rev89_plane29_mem : rev89_plane29 ∈ rev89_planes := by decide
def rev89_plane50 : IntegerPlane := ⟨(-2168356000000),(-51300000000),(-1214821164456)⟩
theorem rev89_plane50_mem : rev89_plane50 ∈ rev89_planes := by decide
def rev89_plane53 : IntegerPlane := ⟨(-824716000000),2112812000000,539054835544⟩
theorem rev89_plane53_mem : rev89_plane53 ∈ rev89_planes := by decide
def rev89_plane74 : IntegerPlane := ⟨824716000000,2112812000000,1573757164456⟩
theorem rev89_plane74_mem : rev89_plane74 ∈ rev89_planes := by decide
def rev89_plane77 : IntegerPlane := ⟨2218132000000,13084000000,1607629024972⟩
theorem rev89_plane77_mem : rev89_plane77 ∈ rev89_planes := by decide
def rev89_vertex0 : FractionPoint := fractionRow89[0]!
theorem rev89_vertex0_mem : rev89_vertex0∈fractionRow89 := by decide
def rev89_vertex1 : FractionPoint := fractionRow89[1]!
theorem rev89_vertex1_mem : rev89_vertex1∈fractionRow89 := by decide
def rev89_vertex2 : FractionPoint := fractionRow89[2]!
theorem rev89_vertex2_mem : rev89_vertex2∈fractionRow89 := by decide
def rev89_vertex3 : FractionPoint := fractionRow89[3]!
theorem rev89_vertex3_mem : rev89_vertex3∈fractionRow89 := by decide
def rev89_vertex4 : FractionPoint := fractionRow89[4]!
theorem rev89_vertex4_mem : rev89_vertex4∈fractionRow89 := by decide
def rev89_s0_ll : FractionPoint := ⟨1044011192867271,1901166327250000,357030466849727,760466530900000⟩
theorem rev89_s0_ll_mem : rev89_s0_ll.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane50 rev89_vertex4 rev89_vertex0 rev89_s0_ll
    rev89_vertex4_mem rev89_vertex0_mem (by decide)
def rev89_s0_lr : FractionPoint := ⟨7654744503,13928000000,6273255497,13928000000⟩
theorem rev89_s0_lr_mem : rev89_s0_lr.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane50 rev89_vertex4 rev89_vertex0 rev89_s0_lr
    rev89_vertex4_mem rev89_vertex0_mem (by decide)
def rev89_s0_ul : FractionPoint := ⟨1044011192867271,1901166327250000,357030466849727,760466530900000⟩
theorem rev89_s0_ul_mem : rev89_s0_ul.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane53 rev89_vertex4 rev89_vertex3 rev89_s0_ul
    rev89_vertex4_mem rev89_vertex3_mem (by decide)
def rev89_s0_ur : FractionPoint := ⟨7654744503,13928000000,691047300849649,1471362276800000⟩
theorem rev89_s0_ur_mem : rev89_s0_ur.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane53 rev89_vertex4 rev89_vertex3 rev89_s0_ur
    rev89_vertex4_mem rev89_vertex3_mem (by decide)
theorem rev89_slab0 (p : Point) (hp : p∈IntegerCarrier rev89_planes)
    (hx0 : rev89_s0_ll.real.1≤p.1) (hx1 : p.1≤rev89_s0_lr.real.1) :
    p∈rationalHull (fractionRow89.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev89_plane50 rev89_plane53 rev89_s0_ll rev89_s0_lr rev89_s0_ul rev89_s0_ur
    (by decide) rev89_s0_ll_mem rev89_s0_lr_mem rev89_s0_ul_mem rev89_s0_ur_mem p
    (hp _ rev89_plane50_mem) (hp _ rev89_plane53_mem) hx0 hx1
def rev89_s1_ll : FractionPoint := ⟨7654744503,13928000000,6273255497,13928000000⟩
theorem rev89_s1_ll_mem : rev89_s1_ll.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane29 rev89_vertex0 rev89_vertex1 rev89_s1_ll
    rev89_vertex0_mem rev89_vertex1_mem (by decide)
def rev89_s1_lr : FractionPoint := ⟨64668895557,103089500000,329836863278747,735311631125000⟩
theorem rev89_s1_lr_mem : rev89_s1_lr.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane29 rev89_vertex0 rev89_vertex1 rev89_s1_lr
    rev89_vertex0_mem rev89_vertex1_mem (by decide)
def rev89_s1_ul : FractionPoint := ⟨7654744503,13928000000,691047300849649,1471362276800000⟩
theorem rev89_s1_ul_mem : rev89_s1_ul.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane53 rev89_vertex4 rev89_vertex3 rev89_s1_ul
    rev89_vertex4_mem rev89_vertex3_mem (by decide)
def rev89_s1_ur : FractionPoint := ⟨64668895557,103089500000,1,2⟩
theorem rev89_s1_ur_mem : rev89_s1_ur.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane53 rev89_vertex4 rev89_vertex3 rev89_s1_ur
    rev89_vertex4_mem rev89_vertex3_mem (by decide)
theorem rev89_slab1 (p : Point) (hp : p∈IntegerCarrier rev89_planes)
    (hx0 : rev89_s1_ll.real.1≤p.1) (hx1 : p.1≤rev89_s1_lr.real.1) :
    p∈rationalHull (fractionRow89.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev89_plane29 rev89_plane53 rev89_s1_ll rev89_s1_lr rev89_s1_ul rev89_s1_ur
    (by decide) rev89_s1_ll_mem rev89_s1_lr_mem rev89_s1_ul_mem rev89_s1_ur_mem p
    (hp _ rev89_plane29_mem) (hp _ rev89_plane53_mem) hx0 hx1
def rev89_s2_ll : FractionPoint := ⟨64668895557,103089500000,329836863278747,735311631125000⟩
theorem rev89_s2_ll_mem : rev89_s2_ll.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane29 rev89_vertex0 rev89_vertex1 rev89_s2_ll
    rev89_vertex0_mem rev89_vertex1_mem (by decide)
def rev89_s2_lr : FractionPoint := ⟨42200335709617487,58446316538000000,744263390061979215047,1667531857145678000000⟩
theorem rev89_s2_lr_mem : rev89_s2_lr.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane29 rev89_vertex0 rev89_vertex1 rev89_s2_lr
    rev89_vertex0_mem rev89_vertex1_mem (by decide)
def rev89_s2_ul : FractionPoint := ⟨64668895557,103089500000,1,2⟩
theorem rev89_s2_ul_mem : rev89_s2_ul.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane74 rev89_vertex3 rev89_vertex2 rev89_s2_ul
    rev89_vertex3_mem rev89_vertex2_mem (by decide)
def rev89_s2_ur : FractionPoint := ⟨42200335709617487,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev89_s2_ur_mem : rev89_s2_ur.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane74 rev89_vertex3 rev89_vertex2 rev89_s2_ur
    rev89_vertex3_mem rev89_vertex2_mem (by decide)
theorem rev89_slab2 (p : Point) (hp : p∈IntegerCarrier rev89_planes)
    (hx0 : rev89_s2_ll.real.1≤p.1) (hx1 : p.1≤rev89_s2_lr.real.1) :
    p∈rationalHull (fractionRow89.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev89_plane29 rev89_plane74 rev89_s2_ll rev89_s2_lr rev89_s2_ul rev89_s2_ur
    (by decide) rev89_s2_ll_mem rev89_s2_lr_mem rev89_s2_ul_mem rev89_s2_ur_mem p
    (hp _ rev89_plane29_mem) (hp _ rev89_plane74_mem) hx0 hx1
def rev89_s3_ll : FractionPoint := ⟨42200335709617487,58446316538000000,744263390061979215047,1667531857145678000000⟩
theorem rev89_s3_ll_mem : rev89_s3_ll.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane29 rev89_vertex0 rev89_vertex1 rev89_s3_ll
    rev89_vertex0_mem rev89_vertex1_mem (by decide)
def rev89_s3_lr : FractionPoint := ⟨11423568365407659,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev89_s3_lr_mem : rev89_s3_lr.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane29 rev89_vertex0 rev89_vertex1 rev89_s3_lr
    rev89_vertex0_mem rev89_vertex1_mem (by decide)
def rev89_s3_ul : FractionPoint := ⟨42200335709617487,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev89_s3_ul_mem : rev89_s3_ul.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane77 rev89_vertex2 rev89_vertex1 rev89_s3_ul
    rev89_vertex2_mem rev89_vertex1_mem (by decide)
def rev89_s3_ur : FractionPoint := ⟨11423568365407659,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev89_s3_ur_mem : rev89_s3_ur.real ∈ rationalHull (fractionRow89.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow89 rev89_plane77 rev89_vertex2 rev89_vertex1 rev89_s3_ur
    rev89_vertex2_mem rev89_vertex1_mem (by decide)
theorem rev89_slab3 (p : Point) (hp : p∈IntegerCarrier rev89_planes)
    (hx0 : rev89_s3_ll.real.1≤p.1) (hx1 : p.1≤rev89_s3_lr.real.1) :
    p∈rationalHull (fractionRow89.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev89_plane29 rev89_plane77 rev89_s3_ll rev89_s3_lr rev89_s3_ul rev89_s3_ur
    (by decide) rev89_s3_ll_mem rev89_s3_lr_mem rev89_s3_ul_mem rev89_s3_ur_mem p
    (hp _ rev89_plane29_mem) (hp _ rev89_plane77_mem) hx0 hx1
theorem rev89_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev89_planes) : rev89_s0_ll.real.1≤p.1 := by
  have hc := rev89_plane50.combine_sound rev89_plane53 2112812000000 51300000000 (by decide) (by decide) p
    (hp _ rev89_plane50_mem) (hp _ rev89_plane53_mem)
  exact (rev89_plane50.combine rev89_plane53 2112812000000 51300000000).xBoundCheck_sound rev89_s0_ll.nx rev89_s0_ll.dx true (by decide) p hc
theorem rev89_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev89_planes) : p.1≤rev89_s3_lr.real.1 := by
  have hc := rev89_plane29.combine_sound rev89_plane77 13084000000 2168356000000 (by decide) (by decide) p
    (hp _ rev89_plane29_mem) (hp _ rev89_plane77_mem)
  exact (rev89_plane29.combine rev89_plane77 13084000000 2168356000000).xBoundCheck_sound rev89_s3_lr.nx rev89_s3_lr.dx false (by decide) p hc
theorem rev89_hull (p : Point) (hp : p∈IntegerCarrier rev89_planes) :
    p∈rationalHull (fractionRow89.map FractionPoint.rational) := by
  have hxlo := rev89_bound0_lo p hp
  have hxhi := rev89_bound0_hi p hp
  by_cases h0 : p.1≤rev89_s0_lr.real.1
  · exact rev89_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev89_s1_lr.real.1
  · exact rev89_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev89_s2_lr.real.1
  · exact rev89_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev89_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull89 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,9,10,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow89 := by
  rw [← fractionRow89_correct]
  exact rev89_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull89
