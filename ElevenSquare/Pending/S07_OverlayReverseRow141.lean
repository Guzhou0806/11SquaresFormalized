import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks17
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev141_planes : List IntegerPlane := integerOverlayPlanes ![9,10,5,6]
def rev141_plane17 : IntegerPlane := ⟨13084000000,2218132000000,1607629024972⟩
theorem rev141_plane17_mem : rev141_plane17 ∈ rev141_planes := by decide
def rev141_plane30 : IntegerPlane := ⟨(-51300000000),(-2168356000000),(-1214821164456)⟩
theorem rev141_plane30_mem : rev141_plane30 ∈ rev141_planes := by decide
def rev141_plane53 : IntegerPlane := ⟨2168356000000,51300000000,1004834835544⟩
theorem rev141_plane53_mem : rev141_plane53 ∈ rev141_planes := by decide
def rev141_plane66 : IntegerPlane := ⟨(-2218132000000),(-13084000000),(-623586975028)⟩
theorem rev141_plane66_mem : rev141_plane66 ∈ rev141_planes := by decide
def rev141_vertex0 : FractionPoint := fractionRow141[0]!
theorem rev141_vertex0_mem : rev141_vertex0∈fractionRow141 := by decide
def rev141_vertex1 : FractionPoint := fractionRow141[1]!
theorem rev141_vertex1_mem : rev141_vertex1∈fractionRow141 := by decide
def rev141_vertex2 : FractionPoint := fractionRow141[2]!
theorem rev141_vertex2_mem : rev141_vertex2∈fractionRow141 := by decide
def rev141_vertex3 : FractionPoint := fractionRow141[3]!
theorem rev141_vertex3_mem : rev141_vertex3∈fractionRow141 := by decide
def rev141_s0_ll : FractionPoint := ⟨50875247919,183754000000,132878752081,183754000000⟩
theorem rev141_s0_ll_mem : rev141_s0_ll.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane66 rev141_vertex3 rev141_vertex0 rev141_s0_ll
    rev141_vertex3_mem rev141_vertex0_mem (by decide)
def rev141_s0_lr : FractionPoint := ⟨4395604732592341,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev141_s0_lr_mem : rev141_s0_lr.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane66 rev141_vertex3 rev141_vertex0 rev141_s0_lr
    rev141_vertex3_mem rev141_vertex0_mem (by decide)
def rev141_s0_ul : FractionPoint := ⟨50875247919,183754000000,132878752081,183754000000⟩
theorem rev141_s0_ul_mem : rev141_s0_ul.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane17 rev141_vertex3 rev141_vertex2 rev141_s0_ul
    rev141_vertex3_mem rev141_vertex2_mem (by decide)
def rev141_s0_ur : FractionPoint := ⟨4395604732592341,15819173098000000,6343462432769948603403,8772253515553234000000⟩
theorem rev141_s0_ur_mem : rev141_s0_ur.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane17 rev141_vertex3 rev141_vertex2 rev141_s0_ur
    rev141_vertex3_mem rev141_vertex2_mem (by decide)
theorem rev141_slab0 (p : Point) (hp : p∈IntegerCarrier rev141_planes)
    (hx0 : rev141_s0_ll.real.1≤p.1) (hx1 : p.1≤rev141_s0_lr.real.1) :
    p∈rationalHull (fractionRow141.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev141_plane66 rev141_plane17 rev141_s0_ll rev141_s0_lr rev141_s0_ul rev141_s0_ur
    (by decide) rev141_s0_ll_mem rev141_s0_lr_mem rev141_s0_ul_mem rev141_s0_ur_mem p
    (hp _ rev141_plane66_mem) (hp _ rev141_plane17_mem) hx0 hx1
def rev141_s1_ll : FractionPoint := ⟨4395604732592341,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev141_s1_ll_mem : rev141_s1_ll.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane30 rev141_vertex0 rev141_vertex1 rev141_s1_ll
    rev141_vertex0_mem rev141_vertex1_mem (by decide)
def rev141_s1_lr : FractionPoint := ⟨7060476758071777,15819173098000000,248095576657293511113,451336827659038000000⟩
theorem rev141_s1_lr_mem : rev141_s1_lr.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane30 rev141_vertex0 rev141_vertex1 rev141_s1_lr
    rev141_vertex0_mem rev141_vertex1_mem (by decide)
def rev141_s1_ul : FractionPoint := ⟨4395604732592341,15819173098000000,6343462432769948603403,8772253515553234000000⟩
theorem rev141_s1_ul_mem : rev141_s1_ul.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane17 rev141_vertex3 rev141_vertex2 rev141_s1_ul
    rev141_vertex3_mem rev141_vertex2_mem (by decide)
def rev141_s1_ur : FractionPoint := ⟨7060476758071777,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev141_s1_ur_mem : rev141_s1_ur.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane17 rev141_vertex3 rev141_vertex2 rev141_s1_ur
    rev141_vertex3_mem rev141_vertex2_mem (by decide)
theorem rev141_slab1 (p : Point) (hp : p∈IntegerCarrier rev141_planes)
    (hx0 : rev141_s1_ll.real.1≤p.1) (hx1 : p.1≤rev141_s1_lr.real.1) :
    p∈rationalHull (fractionRow141.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev141_plane30 rev141_plane17 rev141_s1_ll rev141_s1_lr rev141_s1_ul rev141_s1_ur
    (by decide) rev141_s1_ll_mem rev141_s1_lr_mem rev141_s1_ul_mem rev141_s1_ur_mem p
    (hp _ rev141_plane30_mem) (hp _ rev141_plane17_mem) hx0 hx1
def rev141_s2_ll : FractionPoint := ⟨7060476758071777,15819173098000000,248095576657293511113,451336827659038000000⟩
theorem rev141_s2_ll_mem : rev141_s2_ll.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane30 rev141_vertex0 rev141_vertex1 rev141_s2_ll
    rev141_vertex0_mem rev141_vertex1_mem (by decide)
def rev141_s2_lr : FractionPoint := ⟨6273255497,13928000000,7654744503,13928000000⟩
theorem rev141_s2_lr_mem : rev141_s2_lr.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane30 rev141_vertex0 rev141_vertex1 rev141_s2_lr
    rev141_vertex0_mem rev141_vertex1_mem (by decide)
def rev141_s2_ul : FractionPoint := ⟨7060476758071777,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev141_s2_ul_mem : rev141_s2_ul.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane53 rev141_vertex2 rev141_vertex1 rev141_s2_ul
    rev141_vertex2_mem rev141_vertex1_mem (by decide)
def rev141_s2_ur : FractionPoint := ⟨6273255497,13928000000,7654744503,13928000000⟩
theorem rev141_s2_ur_mem : rev141_s2_ur.real ∈ rationalHull (fractionRow141.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow141 rev141_plane53 rev141_vertex2 rev141_vertex1 rev141_s2_ur
    rev141_vertex2_mem rev141_vertex1_mem (by decide)
theorem rev141_slab2 (p : Point) (hp : p∈IntegerCarrier rev141_planes)
    (hx0 : rev141_s2_ll.real.1≤p.1) (hx1 : p.1≤rev141_s2_lr.real.1) :
    p∈rationalHull (fractionRow141.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev141_plane30 rev141_plane53 rev141_s2_ll rev141_s2_lr rev141_s2_ul rev141_s2_ur
    (by decide) rev141_s2_ll_mem rev141_s2_lr_mem rev141_s2_ul_mem rev141_s2_ur_mem p
    (hp _ rev141_plane30_mem) (hp _ rev141_plane53_mem) hx0 hx1
theorem rev141_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev141_planes) : rev141_s0_ll.real.1≤p.1 := by
  have hc := rev141_plane17.combine_sound rev141_plane66 13084000000 2218132000000 (by decide) (by decide) p
    (hp _ rev141_plane17_mem) (hp _ rev141_plane66_mem)
  exact (rev141_plane17.combine rev141_plane66 13084000000 2218132000000).xBoundCheck_sound rev141_s0_ll.nx rev141_s0_ll.dx true (by decide) p hc
theorem rev141_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev141_planes) : p.1≤rev141_s2_lr.real.1 := by
  have hc := rev141_plane30.combine_sound rev141_plane53 51300000000 2168356000000 (by decide) (by decide) p
    (hp _ rev141_plane30_mem) (hp _ rev141_plane53_mem)
  exact (rev141_plane30.combine rev141_plane53 51300000000 2168356000000).xBoundCheck_sound rev141_s2_lr.nx rev141_s2_lr.dx false (by decide) p hc
theorem rev141_hull (p : Point) (hp : p∈IntegerCarrier rev141_planes) :
    p∈rationalHull (fractionRow141.map FractionPoint.rational) := by
  have hxlo := rev141_bound0_lo p hp
  have hxhi := rev141_bound0_hi p hp
  by_cases h0 : p.1≤rev141_s0_lr.real.1
  · exact rev141_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev141_s1_lr.real.1
  · exact rev141_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev141_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull141 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,10,5,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow141 := by
  rw [← fractionRow141_correct]
  exact rev141_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull141
