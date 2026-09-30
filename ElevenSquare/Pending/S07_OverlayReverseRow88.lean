import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks11
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev88_planes : List IntegerPlane := integerOverlayPlanes ![6,9,9,10]
def rev88_plane14 : IntegerPlane := ⟨(-51300000000),2168356000000,1163521164456⟩
theorem rev88_plane14_mem : rev88_plane14 ∈ rev88_planes := by decide
def rev88_plane54 : IntegerPlane := ⟨824716000000,(-2112812000000),(-539054835544)⟩
theorem rev88_plane54_mem : rev88_plane54 ∈ rev88_planes := by decide
def rev88_plane57 : IntegerPlane := ⟨2218132000000,(-13084000000),1594545024972⟩
theorem rev88_plane57_mem : rev88_plane57 ∈ rev88_planes := by decide
def rev88_plane70 : IntegerPlane := ⟨(-2168356000000),51300000000,(-1163521164456)⟩
theorem rev88_plane70_mem : rev88_plane70 ∈ rev88_planes := by decide
def rev88_plane73 : IntegerPlane := ⟨(-824716000000),(-2112812000000),(-1573757164456)⟩
theorem rev88_plane73_mem : rev88_plane73 ∈ rev88_planes := by decide
def rev88_vertex0 : FractionPoint := fractionRow88[0]!
theorem rev88_vertex0_mem : rev88_vertex0∈fractionRow88 := by decide
def rev88_vertex1 : FractionPoint := fractionRow88[1]!
theorem rev88_vertex1_mem : rev88_vertex1∈fractionRow88 := by decide
def rev88_vertex2 : FractionPoint := fractionRow88[2]!
theorem rev88_vertex2_mem : rev88_vertex2∈fractionRow88 := by decide
def rev88_vertex3 : FractionPoint := fractionRow88[3]!
theorem rev88_vertex3_mem : rev88_vertex3∈fractionRow88 := by decide
def rev88_vertex4 : FractionPoint := fractionRow88[4]!
theorem rev88_vertex4_mem : rev88_vertex4∈fractionRow88 := by decide
def rev88_s0_ll : FractionPoint := ⟨1044011192867271,1901166327250000,403436064050273,760466530900000⟩
theorem rev88_s0_ll_mem : rev88_s0_ll.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane73 rev88_vertex4 rev88_vertex0 rev88_s0_ll
    rev88_vertex4_mem rev88_vertex0_mem (by decide)
def rev88_s0_lr : FractionPoint := ⟨7654744503,13928000000,780314975950351,1471362276800000⟩
theorem rev88_s0_lr_mem : rev88_s0_lr.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane73 rev88_vertex4 rev88_vertex0 rev88_s0_lr
    rev88_vertex4_mem rev88_vertex0_mem (by decide)
def rev88_s0_ul : FractionPoint := ⟨1044011192867271,1901166327250000,403436064050273,760466530900000⟩
theorem rev88_s0_ul_mem : rev88_s0_ul.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane70 rev88_vertex4 rev88_vertex3 rev88_s0_ul
    rev88_vertex4_mem rev88_vertex3_mem (by decide)
def rev88_s0_ur : FractionPoint := ⟨7654744503,13928000000,7654744503,13928000000⟩
theorem rev88_s0_ur_mem : rev88_s0_ur.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane70 rev88_vertex4 rev88_vertex3 rev88_s0_ur
    rev88_vertex4_mem rev88_vertex3_mem (by decide)
theorem rev88_slab0 (p : Point) (hp : p∈IntegerCarrier rev88_planes)
    (hx0 : rev88_s0_ll.real.1≤p.1) (hx1 : p.1≤rev88_s0_lr.real.1) :
    p∈rationalHull (fractionRow88.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev88_plane73 rev88_plane70 rev88_s0_ll rev88_s0_lr rev88_s0_ul rev88_s0_ur
    (by decide) rev88_s0_ll_mem rev88_s0_lr_mem rev88_s0_ul_mem rev88_s0_ur_mem p
    (hp _ rev88_plane73_mem) (hp _ rev88_plane70_mem) hx0 hx1
def rev88_s1_ll : FractionPoint := ⟨7654744503,13928000000,780314975950351,1471362276800000⟩
theorem rev88_s1_ll_mem : rev88_s1_ll.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane73 rev88_vertex4 rev88_vertex0 rev88_s1_ll
    rev88_vertex4_mem rev88_vertex0_mem (by decide)
def rev88_s1_lr : FractionPoint := ⟨64668895557,103089500000,1,2⟩
theorem rev88_s1_lr_mem : rev88_s1_lr.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane73 rev88_vertex4 rev88_vertex0 rev88_s1_lr
    rev88_vertex4_mem rev88_vertex0_mem (by decide)
def rev88_s1_ul : FractionPoint := ⟨7654744503,13928000000,7654744503,13928000000⟩
theorem rev88_s1_ul_mem : rev88_s1_ul.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane14 rev88_vertex3 rev88_vertex2 rev88_s1_ul
    rev88_vertex3_mem rev88_vertex2_mem (by decide)
def rev88_s1_ur : FractionPoint := ⟨64668895557,103089500000,405474767846253,735311631125000⟩
theorem rev88_s1_ur_mem : rev88_s1_ur.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane14 rev88_vertex3 rev88_vertex2 rev88_s1_ur
    rev88_vertex3_mem rev88_vertex2_mem (by decide)
theorem rev88_slab1 (p : Point) (hp : p∈IntegerCarrier rev88_planes)
    (hx0 : rev88_s1_ll.real.1≤p.1) (hx1 : p.1≤rev88_s1_lr.real.1) :
    p∈rationalHull (fractionRow88.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev88_plane73 rev88_plane14 rev88_s1_ll rev88_s1_lr rev88_s1_ul rev88_s1_ur
    (by decide) rev88_s1_ll_mem rev88_s1_lr_mem rev88_s1_ul_mem rev88_s1_ur_mem p
    (hp _ rev88_plane73_mem) (hp _ rev88_plane14_mem) hx0 hx1
def rev88_s2_ll : FractionPoint := ⟨64668895557,103089500000,1,2⟩
theorem rev88_s2_ll_mem : rev88_s2_ll.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane54 rev88_vertex0 rev88_vertex1 rev88_s2_ll
    rev88_vertex0_mem rev88_vertex1_mem (by decide)
def rev88_s2_lr : FractionPoint := ⟨42200335709617487,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev88_s2_lr_mem : rev88_s2_lr.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane54 rev88_vertex0 rev88_vertex1 rev88_s2_lr
    rev88_vertex0_mem rev88_vertex1_mem (by decide)
def rev88_s2_ul : FractionPoint := ⟨64668895557,103089500000,405474767846253,735311631125000⟩
theorem rev88_s2_ul_mem : rev88_s2_ul.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane14 rev88_vertex3 rev88_vertex2 rev88_s2_ul
    rev88_vertex3_mem rev88_vertex2_mem (by decide)
def rev88_s2_ur : FractionPoint := ⟨42200335709617487,58446316538000000,923268467083698784953,1667531857145678000000⟩
theorem rev88_s2_ur_mem : rev88_s2_ur.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane14 rev88_vertex3 rev88_vertex2 rev88_s2_ur
    rev88_vertex3_mem rev88_vertex2_mem (by decide)
theorem rev88_slab2 (p : Point) (hp : p∈IntegerCarrier rev88_planes)
    (hx0 : rev88_s2_ll.real.1≤p.1) (hx1 : p.1≤rev88_s2_lr.real.1) :
    p∈rationalHull (fractionRow88.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev88_plane54 rev88_plane14 rev88_s2_ll rev88_s2_lr rev88_s2_ul rev88_s2_ur
    (by decide) rev88_s2_ll_mem rev88_s2_lr_mem rev88_s2_ul_mem rev88_s2_ur_mem p
    (hp _ rev88_plane54_mem) (hp _ rev88_plane14_mem) hx0 hx1
def rev88_s3_ll : FractionPoint := ⟨42200335709617487,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev88_s3_ll_mem : rev88_s3_ll.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane57 rev88_vertex1 rev88_vertex2 rev88_s3_ll
    rev88_vertex1_mem rev88_vertex2_mem (by decide)
def rev88_s3_lr : FractionPoint := ⟨11423568365407659,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev88_s3_lr_mem : rev88_s3_lr.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane57 rev88_vertex1 rev88_vertex2 rev88_s3_lr
    rev88_vertex1_mem rev88_vertex2_mem (by decide)
def rev88_s3_ul : FractionPoint := ⟨42200335709617487,58446316538000000,923268467083698784953,1667531857145678000000⟩
theorem rev88_s3_ul_mem : rev88_s3_ul.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane14 rev88_vertex3 rev88_vertex2 rev88_s3_ul
    rev88_vertex3_mem rev88_vertex2_mem (by decide)
def rev88_s3_ur : FractionPoint := ⟨11423568365407659,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev88_s3_ur_mem : rev88_s3_ur.real ∈ rationalHull (fractionRow88.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow88 rev88_plane14 rev88_vertex3 rev88_vertex2 rev88_s3_ur
    rev88_vertex3_mem rev88_vertex2_mem (by decide)
theorem rev88_slab3 (p : Point) (hp : p∈IntegerCarrier rev88_planes)
    (hx0 : rev88_s3_ll.real.1≤p.1) (hx1 : p.1≤rev88_s3_lr.real.1) :
    p∈rationalHull (fractionRow88.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev88_plane57 rev88_plane14 rev88_s3_ll rev88_s3_lr rev88_s3_ul rev88_s3_ur
    (by decide) rev88_s3_ll_mem rev88_s3_lr_mem rev88_s3_ul_mem rev88_s3_ur_mem p
    (hp _ rev88_plane57_mem) (hp _ rev88_plane14_mem) hx0 hx1
theorem rev88_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev88_planes) : rev88_s0_ll.real.1≤p.1 := by
  have hc := rev88_plane70.combine_sound rev88_plane73 2112812000000 51300000000 (by decide) (by decide) p
    (hp _ rev88_plane70_mem) (hp _ rev88_plane73_mem)
  exact (rev88_plane70.combine rev88_plane73 2112812000000 51300000000).xBoundCheck_sound rev88_s0_ll.nx rev88_s0_ll.dx true (by decide) p hc
theorem rev88_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev88_planes) : p.1≤rev88_s3_lr.real.1 := by
  have hc := rev88_plane14.combine_sound rev88_plane57 13084000000 2168356000000 (by decide) (by decide) p
    (hp _ rev88_plane14_mem) (hp _ rev88_plane57_mem)
  exact (rev88_plane14.combine rev88_plane57 13084000000 2168356000000).xBoundCheck_sound rev88_s3_lr.nx rev88_s3_lr.dx false (by decide) p hc
theorem rev88_hull (p : Point) (hp : p∈IntegerCarrier rev88_planes) :
    p∈rationalHull (fractionRow88.map FractionPoint.rational) := by
  have hxlo := rev88_bound0_lo p hp
  have hxhi := rev88_bound0_hi p hp
  by_cases h0 : p.1≤rev88_s0_lr.real.1
  · exact rev88_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev88_s1_lr.real.1
  · exact rev88_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev88_s2_lr.real.1
  · exact rev88_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev88_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull88 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,9,9,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow88 := by
  rw [← fractionRow88_correct]
  exact rev88_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull88
