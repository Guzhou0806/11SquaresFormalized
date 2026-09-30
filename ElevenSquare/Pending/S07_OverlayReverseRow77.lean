import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks9
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev77_planes : List IntegerPlane := integerOverlayPlanes ![6,5,6,9]
def rev77_plane6 : IntegerPlane := ⟨(-13084000000),(-2218132000000),(-623586975028)⟩
theorem rev77_plane6_mem : rev77_plane6 ∈ rev77_planes := by decide
def rev77_plane9 : IntegerPlane := ⟨(-2112812000000),(-824716000000),(-1363770835544)⟩
theorem rev77_plane9_mem : rev77_plane9 ∈ rev77_planes := by decide
def rev77_plane30 : IntegerPlane := ⟨(-2112812000000),824716000000,(-749041164456)⟩
theorem rev77_plane30_mem : rev77_plane30 ∈ rev77_planes := by decide
def rev77_plane33 : IntegerPlane := ⟨51300000000,2168356000000,1004834835544⟩
theorem rev77_plane33_mem : rev77_plane33 ∈ rev77_planes := by decide
def rev77_plane54 : IntegerPlane := ⟨2168356000000,51300000000,1214821164456⟩
theorem rev77_plane54_mem : rev77_plane54 ∈ rev77_planes := by decide
def rev77_vertex0 : FractionPoint := fractionRow77[0]!
theorem rev77_vertex0_mem : rev77_vertex0∈fractionRow77 := by decide
def rev77_vertex1 : FractionPoint := fractionRow77[1]!
theorem rev77_vertex1_mem : rev77_vertex1∈fractionRow77 := by decide
def rev77_vertex2 : FractionPoint := fractionRow77[2]!
theorem rev77_vertex2_mem : rev77_vertex2∈fractionRow77 := by decide
def rev77_vertex3 : FractionPoint := fractionRow77[3]!
theorem rev77_vertex3_mem : rev77_vertex3∈fractionRow77 := by decide
def rev77_vertex4 : FractionPoint := fractionRow77[4]!
theorem rev77_vertex4_mem : rev77_vertex4∈fractionRow77 := by decide
def rev77_s0_ll : FractionPoint := ⟨1,2,38420604443,103089500000⟩
theorem rev77_s0_ll_mem : rev77_s0_ll.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane9 rev77_vertex0 rev77_vertex1 rev77_s0_ll
    rev77_vertex0_mem rev77_vertex1_mem (by decide)
def rev77_s0_lr : FractionPoint := ⟨403436064050273,760466530900000,28862112326649171349,97995143046519437500⟩
theorem rev77_s0_lr_mem : rev77_s0_lr.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane9 rev77_vertex0 rev77_vertex1 rev77_s0_lr
    rev77_vertex0_mem rev77_vertex1_mem (by decide)
def rev77_s0_ul : FractionPoint := ⟨1,2,38420604443,103089500000⟩
theorem rev77_s0_ul_mem : rev77_s0_ul.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane30 rev77_vertex0 rev77_vertex4 rev77_s0_ul
    rev77_vertex0_mem rev77_vertex4_mem (by decide)
def rev77_s0_ur : FractionPoint := ⟨403436064050273,760466530900000,857155134382729,1901166327250000⟩
theorem rev77_s0_ur_mem : rev77_s0_ur.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane30 rev77_vertex0 rev77_vertex4 rev77_s0_ur
    rev77_vertex0_mem rev77_vertex4_mem (by decide)
theorem rev77_slab0 (p : Point) (hp : p∈IntegerCarrier rev77_planes)
    (hx0 : rev77_s0_ll.real.1≤p.1) (hx1 : p.1≤rev77_s0_lr.real.1) :
    p∈rationalHull (fractionRow77.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev77_plane9 rev77_plane30 rev77_s0_ll rev77_s0_lr rev77_s0_ul rev77_s0_ur
    (by decide) rev77_s0_ll_mem rev77_s0_lr_mem rev77_s0_ul_mem rev77_s0_ur_mem p
    (hp _ rev77_plane9_mem) (hp _ rev77_plane30_mem) hx0 hx1
def rev77_s1_ll : FractionPoint := ⟨403436064050273,760466530900000,28862112326649171349,97995143046519437500⟩
theorem rev77_s1_ll_mem : rev77_s1_ll.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane9 rev77_vertex0 rev77_vertex1 rev77_s1_ll
    rev77_vertex0_mem rev77_vertex1_mem (by decide)
def rev77_s1_lr : FractionPoint := ⟨31384269691121147,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev77_s1_lr_mem : rev77_s1_lr.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane9 rev77_vertex0 rev77_vertex1 rev77_s1_lr
    rev77_vertex0_mem rev77_vertex1_mem (by decide)
def rev77_s1_ul : FractionPoint := ⟨403436064050273,760466530900000,857155134382729,1901166327250000⟩
theorem rev77_s1_ul_mem : rev77_s1_ul.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane33 rev77_vertex4 rev77_vertex3 rev77_s1_ul
    rev77_vertex4_mem rev77_vertex3_mem (by decide)
def rev77_s1_ur : FractionPoint := ⟨31384269691121147,58446316538000000,751564234624464244547,1667531857145678000000⟩
theorem rev77_s1_ur_mem : rev77_s1_ur.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane33 rev77_vertex4 rev77_vertex3 rev77_s1_ur
    rev77_vertex4_mem rev77_vertex3_mem (by decide)
theorem rev77_slab1 (p : Point) (hp : p∈IntegerCarrier rev77_planes)
    (hx0 : rev77_s1_ll.real.1≤p.1) (hx1 : p.1≤rev77_s1_lr.real.1) :
    p∈rationalHull (fractionRow77.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev77_plane9 rev77_plane33 rev77_s1_ll rev77_s1_lr rev77_s1_ul rev77_s1_ur
    (by decide) rev77_s1_ll_mem rev77_s1_lr_mem rev77_s1_ul_mem rev77_s1_ur_mem p
    (hp _ rev77_plane9_mem) (hp _ rev77_plane33_mem) hx0 hx1
def rev77_s2_ll : FractionPoint := ⟨31384269691121147,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev77_s2_ll_mem : rev77_s2_ll.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane6 rev77_vertex1 rev77_vertex2 rev77_s2_ll
    rev77_vertex1_mem rev77_vertex2_mem (by decide)
def rev77_s2_lr : FractionPoint := ⟨7654744503,13928000000,2146291177778183,7723535624000000⟩
theorem rev77_s2_lr_mem : rev77_s2_lr.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane6 rev77_vertex1 rev77_vertex2 rev77_s2_lr
    rev77_vertex1_mem rev77_vertex2_mem (by decide)
def rev77_s2_ul : FractionPoint := ⟨31384269691121147,58446316538000000,751564234624464244547,1667531857145678000000⟩
theorem rev77_s2_ul_mem : rev77_s2_ul.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane33 rev77_vertex4 rev77_vertex3 rev77_s2_ul
    rev77_vertex4_mem rev77_vertex3_mem (by decide)
def rev77_s2_ur : FractionPoint := ⟨7654744503,13928000000,6273255497,13928000000⟩
theorem rev77_s2_ur_mem : rev77_s2_ur.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane33 rev77_vertex4 rev77_vertex3 rev77_s2_ur
    rev77_vertex4_mem rev77_vertex3_mem (by decide)
theorem rev77_slab2 (p : Point) (hp : p∈IntegerCarrier rev77_planes)
    (hx0 : rev77_s2_ll.real.1≤p.1) (hx1 : p.1≤rev77_s2_lr.real.1) :
    p∈rationalHull (fractionRow77.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev77_plane6 rev77_plane33 rev77_s2_ll rev77_s2_lr rev77_s2_ul rev77_s2_ur
    (by decide) rev77_s2_ll_mem rev77_s2_lr_mem rev77_s2_ul_mem rev77_s2_ur_mem p
    (hp _ rev77_plane6_mem) (hp _ rev77_plane33_mem) hx0 hx1
def rev77_s3_ll : FractionPoint := ⟨7654744503,13928000000,2146291177778183,7723535624000000⟩
theorem rev77_s3_ll_mem : rev77_s3_ll.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane6 rev77_vertex1 rev77_vertex2 rev77_s3_ll
    rev77_vertex1_mem rev77_vertex2_mem (by decide)
def rev77_s3_lr : FractionPoint := ⟨8758696339928223,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev77_s3_lr_mem : rev77_s3_lr.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane6 rev77_vertex1 rev77_vertex2 rev77_s3_lr
    rev77_vertex1_mem rev77_vertex2_mem (by decide)
def rev77_s3_ul : FractionPoint := ⟨7654744503,13928000000,6273255497,13928000000⟩
theorem rev77_s3_ul_mem : rev77_s3_ul.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane54 rev77_vertex3 rev77_vertex2 rev77_s3_ul
    rev77_vertex3_mem rev77_vertex2_mem (by decide)
def rev77_s3_ur : FractionPoint := ⟨8758696339928223,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev77_s3_ur_mem : rev77_s3_ur.real ∈ rationalHull (fractionRow77.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow77 rev77_plane54 rev77_vertex3 rev77_vertex2 rev77_s3_ur
    rev77_vertex3_mem rev77_vertex2_mem (by decide)
theorem rev77_slab3 (p : Point) (hp : p∈IntegerCarrier rev77_planes)
    (hx0 : rev77_s3_ll.real.1≤p.1) (hx1 : p.1≤rev77_s3_lr.real.1) :
    p∈rationalHull (fractionRow77.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev77_plane6 rev77_plane54 rev77_s3_ll rev77_s3_lr rev77_s3_ul rev77_s3_ur
    (by decide) rev77_s3_ll_mem rev77_s3_lr_mem rev77_s3_ul_mem rev77_s3_ur_mem p
    (hp _ rev77_plane6_mem) (hp _ rev77_plane54_mem) hx0 hx1
theorem rev77_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev77_planes) : rev77_s0_ll.real.1≤p.1 := by
  have hc := rev77_plane9.combine_sound rev77_plane30 824716000000 824716000000 (by decide) (by decide) p
    (hp _ rev77_plane9_mem) (hp _ rev77_plane30_mem)
  exact (rev77_plane9.combine rev77_plane30 824716000000 824716000000).xBoundCheck_sound rev77_s0_ll.nx rev77_s0_ll.dx true (by decide) p hc
theorem rev77_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev77_planes) : p.1≤rev77_s3_lr.real.1 := by
  have hc := rev77_plane6.combine_sound rev77_plane54 51300000000 2218132000000 (by decide) (by decide) p
    (hp _ rev77_plane6_mem) (hp _ rev77_plane54_mem)
  exact (rev77_plane6.combine rev77_plane54 51300000000 2218132000000).xBoundCheck_sound rev77_s3_lr.nx rev77_s3_lr.dx false (by decide) p hc
theorem rev77_hull (p : Point) (hp : p∈IntegerCarrier rev77_planes) :
    p∈rationalHull (fractionRow77.map FractionPoint.rational) := by
  have hxlo := rev77_bound0_lo p hp
  have hxhi := rev77_bound0_hi p hp
  by_cases h0 : p.1≤rev77_s0_lr.real.1
  · exact rev77_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev77_s1_lr.real.1
  · exact rev77_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev77_s2_lr.real.1
  · exact rev77_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev77_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull77 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,5,6,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow77 := by
  rw [← fractionRow77_correct]
  exact rev77_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull77
