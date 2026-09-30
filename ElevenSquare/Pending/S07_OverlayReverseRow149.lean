import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks18
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev149_planes : List IntegerPlane := integerOverlayPlanes ![10,9,9,6]
def rev149_plane10 : IntegerPlane := ⟨51300000000,(-2168356000000),(-1163521164456)⟩
theorem rev149_plane10_mem : rev149_plane10 ∈ rev149_planes := by decide
def rev149_plane13 : IntegerPlane := ⟨(-2112812000000),(-824716000000),(-1573757164456)⟩
theorem rev149_plane13_mem : rev149_plane13 ∈ rev149_planes := by decide
def rev149_plane34 : IntegerPlane := ⟨(-2112812000000),824716000000,(-539054835544)⟩
theorem rev149_plane34_mem : rev149_plane34 ∈ rev149_planes := by decide
def rev149_plane37 : IntegerPlane := ⟨(-13084000000),2218132000000,1594545024972⟩
theorem rev149_plane37_mem : rev149_plane37 ∈ rev149_planes := by decide
def rev149_plane74 : IntegerPlane := ⟨2168356000000,(-51300000000),1163521164456⟩
theorem rev149_plane74_mem : rev149_plane74 ∈ rev149_planes := by decide
def rev149_vertex0 : FractionPoint := fractionRow149[0]!
theorem rev149_vertex0_mem : rev149_vertex0∈fractionRow149 := by decide
def rev149_vertex1 : FractionPoint := fractionRow149[1]!
theorem rev149_vertex1_mem : rev149_vertex1∈fractionRow149 := by decide
def rev149_vertex2 : FractionPoint := fractionRow149[2]!
theorem rev149_vertex2_mem : rev149_vertex2∈fractionRow149 := by decide
def rev149_vertex3 : FractionPoint := fractionRow149[3]!
theorem rev149_vertex3_mem : rev149_vertex3∈fractionRow149 := by decide
def rev149_vertex4 : FractionPoint := fractionRow149[4]!
theorem rev149_vertex4_mem : rev149_vertex4∈fractionRow149 := by decide
def rev149_s0_ll : FractionPoint := ⟨1,2,64668895557,103089500000⟩
theorem rev149_s0_ll_mem : rev149_s0_ll.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane13 rev149_vertex0 rev149_vertex1 rev149_s0_ll
    rev149_vertex0_mem rev149_vertex1_mem (by decide)
def rev149_s0_lr : FractionPoint := ⟨403436064050273,760466530900000,1044011192867271,1901166327250000⟩
theorem rev149_s0_lr_mem : rev149_s0_lr.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane13 rev149_vertex0 rev149_vertex1 rev149_s0_lr
    rev149_vertex0_mem rev149_vertex1_mem (by decide)
def rev149_s0_ul : FractionPoint := ⟨1,2,64668895557,103089500000⟩
theorem rev149_s0_ul_mem : rev149_s0_ul.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane34 rev149_vertex0 rev149_vertex4 rev149_s0_ul
    rev149_vertex0_mem rev149_vertex4_mem (by decide)
def rev149_s0_ur : FractionPoint := ⟨403436064050273,760466530900000,69133030719870266151,97995143046519437500⟩
theorem rev149_s0_ur_mem : rev149_s0_ur.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane34 rev149_vertex0 rev149_vertex4 rev149_s0_ur
    rev149_vertex0_mem rev149_vertex4_mem (by decide)
theorem rev149_slab0 (p : Point) (hp : p∈IntegerCarrier rev149_planes)
    (hx0 : rev149_s0_ll.real.1≤p.1) (hx1 : p.1≤rev149_s0_lr.real.1) :
    p∈rationalHull (fractionRow149.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev149_plane13 rev149_plane34 rev149_s0_ll rev149_s0_lr rev149_s0_ul rev149_s0_ur
    (by decide) rev149_s0_ll_mem rev149_s0_lr_mem rev149_s0_ul_mem rev149_s0_ur_mem p
    (hp _ rev149_plane13_mem) (hp _ rev149_plane34_mem) hx0 hx1
def rev149_s1_ll : FractionPoint := ⟨403436064050273,760466530900000,1044011192867271,1901166327250000⟩
theorem rev149_s1_ll_mem : rev149_s1_ll.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane10 rev149_vertex1 rev149_vertex2 rev149_s1_ll
    rev149_vertex1_mem rev149_vertex2_mem (by decide)
def rev149_s1_lr : FractionPoint := ⟨31384269691121147,58446316538000000,915967622521213755453,1667531857145678000000⟩
theorem rev149_s1_lr_mem : rev149_s1_lr.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane10 rev149_vertex1 rev149_vertex2 rev149_s1_lr
    rev149_vertex1_mem rev149_vertex2_mem (by decide)
def rev149_s1_ul : FractionPoint := ⟨403436064050273,760466530900000,69133030719870266151,97995143046519437500⟩
theorem rev149_s1_ul_mem : rev149_s1_ul.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane34 rev149_vertex0 rev149_vertex4 rev149_s1_ul
    rev149_vertex0_mem rev149_vertex4_mem (by decide)
def rev149_s1_ur : FractionPoint := ⟨31384269691121147,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev149_s1_ur_mem : rev149_s1_ur.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane34 rev149_vertex0 rev149_vertex4 rev149_s1_ur
    rev149_vertex0_mem rev149_vertex4_mem (by decide)
theorem rev149_slab1 (p : Point) (hp : p∈IntegerCarrier rev149_planes)
    (hx0 : rev149_s1_ll.real.1≤p.1) (hx1 : p.1≤rev149_s1_lr.real.1) :
    p∈rationalHull (fractionRow149.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev149_plane10 rev149_plane34 rev149_s1_ll rev149_s1_lr rev149_s1_ul rev149_s1_ur
    (by decide) rev149_s1_ll_mem rev149_s1_lr_mem rev149_s1_ul_mem rev149_s1_ur_mem p
    (hp _ rev149_plane10_mem) (hp _ rev149_plane34_mem) hx0 hx1
def rev149_s2_ll : FractionPoint := ⟨31384269691121147,58446316538000000,915967622521213755453,1667531857145678000000⟩
theorem rev149_s2_ll_mem : rev149_s2_ll.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane10 rev149_vertex1 rev149_vertex2 rev149_s2_ll
    rev149_vertex1_mem rev149_vertex2_mem (by decide)
def rev149_s2_lr : FractionPoint := ⟨7654744503,13928000000,7654744503,13928000000⟩
theorem rev149_s2_lr_mem : rev149_s2_lr.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane10 rev149_vertex1 rev149_vertex2 rev149_s2_lr
    rev149_vertex1_mem rev149_vertex2_mem (by decide)
def rev149_s2_ul : FractionPoint := ⟨31384269691121147,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev149_s2_ul_mem : rev149_s2_ul.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane37 rev149_vertex4 rev149_vertex3 rev149_s2_ul
    rev149_vertex4_mem rev149_vertex3_mem (by decide)
def rev149_s2_ur : FractionPoint := ⟨7654744503,13928000000,5577244446221817,7723535624000000⟩
theorem rev149_s2_ur_mem : rev149_s2_ur.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane37 rev149_vertex4 rev149_vertex3 rev149_s2_ur
    rev149_vertex4_mem rev149_vertex3_mem (by decide)
theorem rev149_slab2 (p : Point) (hp : p∈IntegerCarrier rev149_planes)
    (hx0 : rev149_s2_ll.real.1≤p.1) (hx1 : p.1≤rev149_s2_lr.real.1) :
    p∈rationalHull (fractionRow149.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev149_plane10 rev149_plane37 rev149_s2_ll rev149_s2_lr rev149_s2_ul rev149_s2_ur
    (by decide) rev149_s2_ll_mem rev149_s2_lr_mem rev149_s2_ul_mem rev149_s2_ur_mem p
    (hp _ rev149_plane10_mem) (hp _ rev149_plane37_mem) hx0 hx1
def rev149_s3_ll : FractionPoint := ⟨7654744503,13928000000,7654744503,13928000000⟩
theorem rev149_s3_ll_mem : rev149_s3_ll.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane74 rev149_vertex2 rev149_vertex3 rev149_s3_ll
    rev149_vertex2_mem rev149_vertex3_mem (by decide)
def rev149_s3_lr : FractionPoint := ⟨8758696339928223,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev149_s3_lr_mem : rev149_s3_lr.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane74 rev149_vertex2 rev149_vertex3 rev149_s3_lr
    rev149_vertex2_mem rev149_vertex3_mem (by decide)
def rev149_s3_ul : FractionPoint := ⟨7654744503,13928000000,5577244446221817,7723535624000000⟩
theorem rev149_s3_ul_mem : rev149_s3_ul.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane37 rev149_vertex4 rev149_vertex3 rev149_s3_ul
    rev149_vertex4_mem rev149_vertex3_mem (by decide)
def rev149_s3_ur : FractionPoint := ⟨8758696339928223,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev149_s3_ur_mem : rev149_s3_ur.real ∈ rationalHull (fractionRow149.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow149 rev149_plane37 rev149_vertex4 rev149_vertex3 rev149_s3_ur
    rev149_vertex4_mem rev149_vertex3_mem (by decide)
theorem rev149_slab3 (p : Point) (hp : p∈IntegerCarrier rev149_planes)
    (hx0 : rev149_s3_ll.real.1≤p.1) (hx1 : p.1≤rev149_s3_lr.real.1) :
    p∈rationalHull (fractionRow149.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev149_plane74 rev149_plane37 rev149_s3_ll rev149_s3_lr rev149_s3_ul rev149_s3_ur
    (by decide) rev149_s3_ll_mem rev149_s3_lr_mem rev149_s3_ul_mem rev149_s3_ur_mem p
    (hp _ rev149_plane74_mem) (hp _ rev149_plane37_mem) hx0 hx1
theorem rev149_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev149_planes) : rev149_s0_ll.real.1≤p.1 := by
  have hc := rev149_plane13.combine_sound rev149_plane34 824716000000 824716000000 (by decide) (by decide) p
    (hp _ rev149_plane13_mem) (hp _ rev149_plane34_mem)
  exact (rev149_plane13.combine rev149_plane34 824716000000 824716000000).xBoundCheck_sound rev149_s0_ll.nx rev149_s0_ll.dx true (by decide) p hc
theorem rev149_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev149_planes) : p.1≤rev149_s3_lr.real.1 := by
  have hc := rev149_plane37.combine_sound rev149_plane74 51300000000 2218132000000 (by decide) (by decide) p
    (hp _ rev149_plane37_mem) (hp _ rev149_plane74_mem)
  exact (rev149_plane37.combine rev149_plane74 51300000000 2218132000000).xBoundCheck_sound rev149_s3_lr.nx rev149_s3_lr.dx false (by decide) p hc
theorem rev149_hull (p : Point) (hp : p∈IntegerCarrier rev149_planes) :
    p∈rationalHull (fractionRow149.map FractionPoint.rational) := by
  have hxlo := rev149_bound0_lo p hp
  have hxhi := rev149_bound0_hi p hp
  by_cases h0 : p.1≤rev149_s0_lr.real.1
  · exact rev149_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev149_s1_lr.real.1
  · exact rev149_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev149_s2_lr.real.1
  · exact rev149_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev149_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull149 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,9,9,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow149 := by
  rw [← fractionRow149_correct]
  exact rev149_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull149
