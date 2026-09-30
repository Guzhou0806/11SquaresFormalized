import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks17
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev142_planes : List IntegerPlane := integerOverlayPlanes ![9,10,9,6]
def rev142_plane14 : IntegerPlane := ⟨2112812000000,824716000000,1573757164456⟩
theorem rev142_plane14_mem : rev142_plane14 ∈ rev142_planes := by decide
def rev142_plane17 : IntegerPlane := ⟨13084000000,2218132000000,1607629024972⟩
theorem rev142_plane17_mem : rev142_plane17 ∈ rev142_planes := by decide
def rev142_plane30 : IntegerPlane := ⟨(-51300000000),(-2168356000000),(-1214821164456)⟩
theorem rev142_plane30_mem : rev142_plane30 ∈ rev142_planes := by decide
def rev142_plane33 : IntegerPlane := ⟨2112812000000,(-824716000000),539054835544⟩
theorem rev142_plane33_mem : rev142_plane33 ∈ rev142_planes := by decide
def rev142_plane49 : IntegerPlane := ⟨(-2168356000000),(-51300000000),(-1004834835544)⟩
theorem rev142_plane49_mem : rev142_plane49 ∈ rev142_planes := by decide
def rev142_vertex0 : FractionPoint := fractionRow142[0]!
theorem rev142_vertex0_mem : rev142_vertex0∈fractionRow142 := by decide
def rev142_vertex1 : FractionPoint := fractionRow142[1]!
theorem rev142_vertex1_mem : rev142_vertex1∈fractionRow142 := by decide
def rev142_vertex2 : FractionPoint := fractionRow142[2]!
theorem rev142_vertex2_mem : rev142_vertex2∈fractionRow142 := by decide
def rev142_vertex3 : FractionPoint := fractionRow142[3]!
theorem rev142_vertex3_mem : rev142_vertex3∈fractionRow142 := by decide
def rev142_vertex4 : FractionPoint := fractionRow142[4]!
theorem rev142_vertex4_mem : rev142_vertex4∈fractionRow142 := by decide
def rev142_s0_ll : FractionPoint := ⟨7060476758071777,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev142_s0_ll_mem : rev142_s0_ll.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane49 rev142_vertex4 rev142_vertex0 rev142_s0_ll
    rev142_vertex4_mem rev142_vertex0_mem (by decide)
def rev142_s0_lr : FractionPoint := ⟨6273255497,13928000000,7654744503,13928000000⟩
theorem rev142_s0_lr_mem : rev142_s0_lr.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane49 rev142_vertex4 rev142_vertex0 rev142_s0_lr
    rev142_vertex4_mem rev142_vertex0_mem (by decide)
def rev142_s0_ul : FractionPoint := ⟨7060476758071777,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev142_s0_ul_mem : rev142_s0_ul.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane17 rev142_vertex4 rev142_vertex3 rev142_s0_ul
    rev142_vertex4_mem rev142_vertex3_mem (by decide)
def rev142_s0_ur : FractionPoint := ⟨6273255497,13928000000,5577244446221817,7723535624000000⟩
theorem rev142_s0_ur_mem : rev142_s0_ur.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane17 rev142_vertex4 rev142_vertex3 rev142_s0_ur
    rev142_vertex4_mem rev142_vertex3_mem (by decide)
theorem rev142_slab0 (p : Point) (hp : p∈IntegerCarrier rev142_planes)
    (hx0 : rev142_s0_ll.real.1≤p.1) (hx1 : p.1≤rev142_s0_lr.real.1) :
    p∈rationalHull (fractionRow142.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev142_plane49 rev142_plane17 rev142_s0_ll rev142_s0_lr rev142_s0_ul rev142_s0_ur
    (by decide) rev142_s0_ll_mem rev142_s0_lr_mem rev142_s0_ul_mem rev142_s0_ur_mem p
    (hp _ rev142_plane49_mem) (hp _ rev142_plane17_mem) hx0 hx1
def rev142_s1_ll : FractionPoint := ⟨6273255497,13928000000,7654744503,13928000000⟩
theorem rev142_s1_ll_mem : rev142_s1_ll.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane30 rev142_vertex0 rev142_vertex1 rev142_s1_ll
    rev142_vertex0_mem rev142_vertex1_mem (by decide)
def rev142_s1_lr : FractionPoint := ⟨27062046846878853,58446316538000000,915967622521213755453,1667531857145678000000⟩
theorem rev142_s1_lr_mem : rev142_s1_lr.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane30 rev142_vertex0 rev142_vertex1 rev142_s1_lr
    rev142_vertex0_mem rev142_vertex1_mem (by decide)
def rev142_s1_ul : FractionPoint := ⟨6273255497,13928000000,5577244446221817,7723535624000000⟩
theorem rev142_s1_ul_mem : rev142_s1_ul.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane17 rev142_vertex4 rev142_vertex3 rev142_s1_ul
    rev142_vertex4_mem rev142_vertex3_mem (by decide)
def rev142_s1_ur : FractionPoint := ⟨27062046846878853,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev142_s1_ur_mem : rev142_s1_ur.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane17 rev142_vertex4 rev142_vertex3 rev142_s1_ur
    rev142_vertex4_mem rev142_vertex3_mem (by decide)
theorem rev142_slab1 (p : Point) (hp : p∈IntegerCarrier rev142_planes)
    (hx0 : rev142_s1_ll.real.1≤p.1) (hx1 : p.1≤rev142_s1_lr.real.1) :
    p∈rationalHull (fractionRow142.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev142_plane30 rev142_plane17 rev142_s1_ll rev142_s1_lr rev142_s1_ul rev142_s1_ur
    (by decide) rev142_s1_ll_mem rev142_s1_lr_mem rev142_s1_ul_mem rev142_s1_ur_mem p
    (hp _ rev142_plane30_mem) (hp _ rev142_plane17_mem) hx0 hx1
def rev142_s2_ll : FractionPoint := ⟨27062046846878853,58446316538000000,915967622521213755453,1667531857145678000000⟩
theorem rev142_s2_ll_mem : rev142_s2_ll.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane30 rev142_vertex0 rev142_vertex1 rev142_s2_ll
    rev142_vertex0_mem rev142_vertex1_mem (by decide)
def rev142_s2_lr : FractionPoint := ⟨357030466849727,760466530900000,1044011192867271,1901166327250000⟩
theorem rev142_s2_lr_mem : rev142_s2_lr.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane30 rev142_vertex0 rev142_vertex1 rev142_s2_lr
    rev142_vertex0_mem rev142_vertex1_mem (by decide)
def rev142_s2_ul : FractionPoint := ⟨27062046846878853,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev142_s2_ul_mem : rev142_s2_ul.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane14 rev142_vertex3 rev142_vertex2 rev142_s2_ul
    rev142_vertex3_mem rev142_vertex2_mem (by decide)
def rev142_s2_ur : FractionPoint := ⟨357030466849727,760466530900000,69133030719870266151,97995143046519437500⟩
theorem rev142_s2_ur_mem : rev142_s2_ur.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane14 rev142_vertex3 rev142_vertex2 rev142_s2_ur
    rev142_vertex3_mem rev142_vertex2_mem (by decide)
theorem rev142_slab2 (p : Point) (hp : p∈IntegerCarrier rev142_planes)
    (hx0 : rev142_s2_ll.real.1≤p.1) (hx1 : p.1≤rev142_s2_lr.real.1) :
    p∈rationalHull (fractionRow142.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev142_plane30 rev142_plane14 rev142_s2_ll rev142_s2_lr rev142_s2_ul rev142_s2_ur
    (by decide) rev142_s2_ll_mem rev142_s2_lr_mem rev142_s2_ul_mem rev142_s2_ur_mem p
    (hp _ rev142_plane30_mem) (hp _ rev142_plane14_mem) hx0 hx1
def rev142_s3_ll : FractionPoint := ⟨357030466849727,760466530900000,1044011192867271,1901166327250000⟩
theorem rev142_s3_ll_mem : rev142_s3_ll.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane33 rev142_vertex1 rev142_vertex2 rev142_s3_ll
    rev142_vertex1_mem rev142_vertex2_mem (by decide)
def rev142_s3_lr : FractionPoint := ⟨1,2,64668895557,103089500000⟩
theorem rev142_s3_lr_mem : rev142_s3_lr.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane33 rev142_vertex1 rev142_vertex2 rev142_s3_lr
    rev142_vertex1_mem rev142_vertex2_mem (by decide)
def rev142_s3_ul : FractionPoint := ⟨357030466849727,760466530900000,69133030719870266151,97995143046519437500⟩
theorem rev142_s3_ul_mem : rev142_s3_ul.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane14 rev142_vertex3 rev142_vertex2 rev142_s3_ul
    rev142_vertex3_mem rev142_vertex2_mem (by decide)
def rev142_s3_ur : FractionPoint := ⟨1,2,64668895557,103089500000⟩
theorem rev142_s3_ur_mem : rev142_s3_ur.real ∈ rationalHull (fractionRow142.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow142 rev142_plane14 rev142_vertex3 rev142_vertex2 rev142_s3_ur
    rev142_vertex3_mem rev142_vertex2_mem (by decide)
theorem rev142_slab3 (p : Point) (hp : p∈IntegerCarrier rev142_planes)
    (hx0 : rev142_s3_ll.real.1≤p.1) (hx1 : p.1≤rev142_s3_lr.real.1) :
    p∈rationalHull (fractionRow142.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev142_plane33 rev142_plane14 rev142_s3_ll rev142_s3_lr rev142_s3_ul rev142_s3_ur
    (by decide) rev142_s3_ll_mem rev142_s3_lr_mem rev142_s3_ul_mem rev142_s3_ur_mem p
    (hp _ rev142_plane33_mem) (hp _ rev142_plane14_mem) hx0 hx1
theorem rev142_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev142_planes) : rev142_s0_ll.real.1≤p.1 := by
  have hc := rev142_plane17.combine_sound rev142_plane49 51300000000 2218132000000 (by decide) (by decide) p
    (hp _ rev142_plane17_mem) (hp _ rev142_plane49_mem)
  exact (rev142_plane17.combine rev142_plane49 51300000000 2218132000000).xBoundCheck_sound rev142_s0_ll.nx rev142_s0_ll.dx true (by decide) p hc
theorem rev142_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev142_planes) : p.1≤rev142_s3_lr.real.1 := by
  have hc := rev142_plane14.combine_sound rev142_plane33 824716000000 824716000000 (by decide) (by decide) p
    (hp _ rev142_plane14_mem) (hp _ rev142_plane33_mem)
  exact (rev142_plane14.combine rev142_plane33 824716000000 824716000000).xBoundCheck_sound rev142_s3_lr.nx rev142_s3_lr.dx false (by decide) p hc
theorem rev142_hull (p : Point) (hp : p∈IntegerCarrier rev142_planes) :
    p∈rationalHull (fractionRow142.map FractionPoint.rational) := by
  have hxlo := rev142_bound0_lo p hp
  have hxhi := rev142_bound0_hi p hp
  by_cases h0 : p.1≤rev142_s0_lr.real.1
  · exact rev142_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev142_s1_lr.real.1
  · exact rev142_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev142_s2_lr.real.1
  · exact rev142_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev142_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull142 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,10,9,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow142 := by
  rw [← fractionRow142_correct]
  exact rev142_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull142
