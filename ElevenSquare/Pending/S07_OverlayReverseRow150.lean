import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks18
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev150_planes : List IntegerPlane := integerOverlayPlanes ![10,9,9,10]
def rev150_plane10 : IntegerPlane := ⟨51300000000,(-2168356000000),(-1163521164456)⟩
theorem rev150_plane10_mem : rev150_plane10 ∈ rev150_planes := by decide
def rev150_plane37 : IntegerPlane := ⟨(-13084000000),2218132000000,1594545024972⟩
theorem rev150_plane37_mem : rev150_plane37 ∈ rev150_planes := by decide
def rev150_plane57 : IntegerPlane := ⟨2218132000000,(-13084000000),1594545024972⟩
theorem rev150_plane57_mem : rev150_plane57 ∈ rev150_planes := by decide
def rev150_plane70 : IntegerPlane := ⟨(-2168356000000),51300000000,(-1163521164456)⟩
theorem rev150_plane70_mem : rev150_plane70 ∈ rev150_planes := by decide
def rev150_vertex0 : FractionPoint := fractionRow150[0]!
theorem rev150_vertex0_mem : rev150_vertex0∈fractionRow150 := by decide
def rev150_vertex1 : FractionPoint := fractionRow150[1]!
theorem rev150_vertex1_mem : rev150_vertex1∈fractionRow150 := by decide
def rev150_vertex2 : FractionPoint := fractionRow150[2]!
theorem rev150_vertex2_mem : rev150_vertex2∈fractionRow150 := by decide
def rev150_vertex3 : FractionPoint := fractionRow150[3]!
theorem rev150_vertex3_mem : rev150_vertex3∈fractionRow150 := by decide
def rev150_s0_ll : FractionPoint := ⟨7654744503,13928000000,7654744503,13928000000⟩
theorem rev150_s0_ll_mem : rev150_s0_ll.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane10 rev150_vertex0 rev150_vertex1 rev150_s0_ll
    rev150_vertex0_mem rev150_vertex1_mem (by decide)
def rev150_s0_lr : FractionPoint := ⟨8758696339928223,15819173098000000,248095576657293511113,451336827659038000000⟩
theorem rev150_s0_lr_mem : rev150_s0_lr.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane10 rev150_vertex0 rev150_vertex1 rev150_s0_lr
    rev150_vertex0_mem rev150_vertex1_mem (by decide)
def rev150_s0_ul : FractionPoint := ⟨7654744503,13928000000,7654744503,13928000000⟩
theorem rev150_s0_ul_mem : rev150_s0_ul.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane70 rev150_vertex0 rev150_vertex3 rev150_s0_ul
    rev150_vertex0_mem rev150_vertex3_mem (by decide)
def rev150_s0_ur : FractionPoint := ⟨8758696339928223,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev150_s0_ur_mem : rev150_s0_ur.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane70 rev150_vertex0 rev150_vertex3 rev150_s0_ur
    rev150_vertex0_mem rev150_vertex3_mem (by decide)
theorem rev150_slab0 (p : Point) (hp : p∈IntegerCarrier rev150_planes)
    (hx0 : rev150_s0_ll.real.1≤p.1) (hx1 : p.1≤rev150_s0_lr.real.1) :
    p∈rationalHull (fractionRow150.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev150_plane10 rev150_plane70 rev150_s0_ll rev150_s0_lr rev150_s0_ul rev150_s0_ur
    (by decide) rev150_s0_ll_mem rev150_s0_lr_mem rev150_s0_ul_mem rev150_s0_ur_mem p
    (hp _ rev150_plane10_mem) (hp _ rev150_plane70_mem) hx0 hx1
def rev150_s1_ll : FractionPoint := ⟨8758696339928223,15819173098000000,248095576657293511113,451336827659038000000⟩
theorem rev150_s1_ll_mem : rev150_s1_ll.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane10 rev150_vertex0 rev150_vertex1 rev150_s1_ll
    rev150_vertex0_mem rev150_vertex1_mem (by decide)
def rev150_s1_lr : FractionPoint := ⟨11423568365407659,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev150_s1_lr_mem : rev150_s1_lr.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane10 rev150_vertex0 rev150_vertex1 rev150_s1_lr
    rev150_vertex0_mem rev150_vertex1_mem (by decide)
def rev150_s1_ul : FractionPoint := ⟨8758696339928223,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev150_s1_ul_mem : rev150_s1_ul.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane37 rev150_vertex3 rev150_vertex2 rev150_s1_ul
    rev150_vertex3_mem rev150_vertex2_mem (by decide)
def rev150_s1_ur : FractionPoint := ⟨11423568365407659,15819173098000000,6343462432769948603403,8772253515553234000000⟩
theorem rev150_s1_ur_mem : rev150_s1_ur.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane37 rev150_vertex3 rev150_vertex2 rev150_s1_ur
    rev150_vertex3_mem rev150_vertex2_mem (by decide)
theorem rev150_slab1 (p : Point) (hp : p∈IntegerCarrier rev150_planes)
    (hx0 : rev150_s1_ll.real.1≤p.1) (hx1 : p.1≤rev150_s1_lr.real.1) :
    p∈rationalHull (fractionRow150.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev150_plane10 rev150_plane37 rev150_s1_ll rev150_s1_lr rev150_s1_ul rev150_s1_ur
    (by decide) rev150_s1_ll_mem rev150_s1_lr_mem rev150_s1_ul_mem rev150_s1_ur_mem p
    (hp _ rev150_plane10_mem) (hp _ rev150_plane37_mem) hx0 hx1
def rev150_s2_ll : FractionPoint := ⟨11423568365407659,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev150_s2_ll_mem : rev150_s2_ll.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane57 rev150_vertex1 rev150_vertex2 rev150_s2_ll
    rev150_vertex1_mem rev150_vertex2_mem (by decide)
def rev150_s2_lr : FractionPoint := ⟨132878752081,183754000000,132878752081,183754000000⟩
theorem rev150_s2_lr_mem : rev150_s2_lr.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane57 rev150_vertex1 rev150_vertex2 rev150_s2_lr
    rev150_vertex1_mem rev150_vertex2_mem (by decide)
def rev150_s2_ul : FractionPoint := ⟨11423568365407659,15819173098000000,6343462432769948603403,8772253515553234000000⟩
theorem rev150_s2_ul_mem : rev150_s2_ul.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane37 rev150_vertex3 rev150_vertex2 rev150_s2_ul
    rev150_vertex3_mem rev150_vertex2_mem (by decide)
def rev150_s2_ur : FractionPoint := ⟨132878752081,183754000000,132878752081,183754000000⟩
theorem rev150_s2_ur_mem : rev150_s2_ur.real ∈ rationalHull (fractionRow150.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow150 rev150_plane37 rev150_vertex3 rev150_vertex2 rev150_s2_ur
    rev150_vertex3_mem rev150_vertex2_mem (by decide)
theorem rev150_slab2 (p : Point) (hp : p∈IntegerCarrier rev150_planes)
    (hx0 : rev150_s2_ll.real.1≤p.1) (hx1 : p.1≤rev150_s2_lr.real.1) :
    p∈rationalHull (fractionRow150.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev150_plane57 rev150_plane37 rev150_s2_ll rev150_s2_lr rev150_s2_ul rev150_s2_ur
    (by decide) rev150_s2_ll_mem rev150_s2_lr_mem rev150_s2_ul_mem rev150_s2_ur_mem p
    (hp _ rev150_plane57_mem) (hp _ rev150_plane37_mem) hx0 hx1
theorem rev150_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev150_planes) : rev150_s0_ll.real.1≤p.1 := by
  have hc := rev150_plane10.combine_sound rev150_plane70 51300000000 2168356000000 (by decide) (by decide) p
    (hp _ rev150_plane10_mem) (hp _ rev150_plane70_mem)
  exact (rev150_plane10.combine rev150_plane70 51300000000 2168356000000).xBoundCheck_sound rev150_s0_ll.nx rev150_s0_ll.dx true (by decide) p hc
theorem rev150_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev150_planes) : p.1≤rev150_s2_lr.real.1 := by
  have hc := rev150_plane37.combine_sound rev150_plane57 13084000000 2218132000000 (by decide) (by decide) p
    (hp _ rev150_plane37_mem) (hp _ rev150_plane57_mem)
  exact (rev150_plane37.combine rev150_plane57 13084000000 2218132000000).xBoundCheck_sound rev150_s2_lr.nx rev150_s2_lr.dx false (by decide) p hc
theorem rev150_hull (p : Point) (hp : p∈IntegerCarrier rev150_planes) :
    p∈rationalHull (fractionRow150.map FractionPoint.rational) := by
  have hxlo := rev150_bound0_lo p hp
  have hxhi := rev150_bound0_hi p hp
  by_cases h0 : p.1≤rev150_s0_lr.real.1
  · exact rev150_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev150_s1_lr.real.1
  · exact rev150_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev150_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull150 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,9,9,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow150 := by
  rw [← fractionRow150_correct]
  exact rev150_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull150
