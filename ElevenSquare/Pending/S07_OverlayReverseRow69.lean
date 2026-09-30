import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks8
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev69_planes : List IntegerPlane := integerOverlayPlanes ![5,6,6,5]
def rev69_plane13 : IntegerPlane := ⟨(-51300000000),2168356000000,953534835544⟩
theorem rev69_plane13_mem : rev69_plane13 ∈ rev69_planes := by decide
def rev69_plane26 : IntegerPlane := ⟨13084000000,(-2218132000000),(-610502975028)⟩
theorem rev69_plane26_mem : rev69_plane26 ∈ rev69_planes := by decide
def rev69_plane46 : IntegerPlane := ⟨(-2218132000000),13084000000,(-610502975028)⟩
theorem rev69_plane46_mem : rev69_plane46 ∈ rev69_planes := by decide
def rev69_plane73 : IntegerPlane := ⟨2168356000000,(-51300000000),953534835544⟩
theorem rev69_plane73_mem : rev69_plane73 ∈ rev69_planes := by decide
def rev69_vertex0 : FractionPoint := fractionRow69[0]!
theorem rev69_vertex0_mem : rev69_vertex0∈fractionRow69 := by decide
def rev69_vertex1 : FractionPoint := fractionRow69[1]!
theorem rev69_vertex1_mem : rev69_vertex1∈fractionRow69 := by decide
def rev69_vertex2 : FractionPoint := fractionRow69[2]!
theorem rev69_vertex2_mem : rev69_vertex2∈fractionRow69 := by decide
def rev69_vertex3 : FractionPoint := fractionRow69[3]!
theorem rev69_vertex3_mem : rev69_vertex3∈fractionRow69 := by decide
def rev69_s0_ll : FractionPoint := ⟨50875247919,183754000000,50875247919,183754000000⟩
theorem rev69_s0_ll_mem : rev69_s0_ll.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane26 rev69_vertex0 rev69_vertex1 rev69_s0_ll
    rev69_vertex0_mem rev69_vertex1_mem (by decide)
def rev69_s0_lr : FractionPoint := ⟨4395604732592341,15819173098000000,2428791082783285396597,8772253515553234000000⟩
theorem rev69_s0_lr_mem : rev69_s0_lr.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane26 rev69_vertex0 rev69_vertex1 rev69_s0_lr
    rev69_vertex0_mem rev69_vertex1_mem (by decide)
def rev69_s0_ul : FractionPoint := ⟨50875247919,183754000000,50875247919,183754000000⟩
theorem rev69_s0_ul_mem : rev69_s0_ul.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane46 rev69_vertex0 rev69_vertex3 rev69_s0_ul
    rev69_vertex0_mem rev69_vertex3_mem (by decide)
def rev69_s0_ur : FractionPoint := ⟨4395604732592341,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev69_s0_ur_mem : rev69_s0_ur.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane46 rev69_vertex0 rev69_vertex3 rev69_s0_ur
    rev69_vertex0_mem rev69_vertex3_mem (by decide)
theorem rev69_slab0 (p : Point) (hp : p∈IntegerCarrier rev69_planes)
    (hx0 : rev69_s0_ll.real.1≤p.1) (hx1 : p.1≤rev69_s0_lr.real.1) :
    p∈rationalHull (fractionRow69.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev69_plane26 rev69_plane46 rev69_s0_ll rev69_s0_lr rev69_s0_ul rev69_s0_ur
    (by decide) rev69_s0_ll_mem rev69_s0_lr_mem rev69_s0_ul_mem rev69_s0_ur_mem p
    (hp _ rev69_plane26_mem) (hp _ rev69_plane46_mem) hx0 hx1
def rev69_s1_ll : FractionPoint := ⟨4395604732592341,15819173098000000,2428791082783285396597,8772253515553234000000⟩
theorem rev69_s1_ll_mem : rev69_s1_ll.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane26 rev69_vertex0 rev69_vertex1 rev69_s1_ll
    rev69_vertex0_mem rev69_vertex1_mem (by decide)
def rev69_s1_lr : FractionPoint := ⟨7060476758071777,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev69_s1_lr_mem : rev69_s1_lr.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane26 rev69_vertex0 rev69_vertex1 rev69_s1_lr
    rev69_vertex0_mem rev69_vertex1_mem (by decide)
def rev69_s1_ul : FractionPoint := ⟨4395604732592341,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev69_s1_ul_mem : rev69_s1_ul.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane13 rev69_vertex3 rev69_vertex2 rev69_s1_ul
    rev69_vertex3_mem rev69_vertex2_mem (by decide)
def rev69_s1_ur : FractionPoint := ⟨7060476758071777,15819173098000000,203241251001744488887,451336827659038000000⟩
theorem rev69_s1_ur_mem : rev69_s1_ur.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane13 rev69_vertex3 rev69_vertex2 rev69_s1_ur
    rev69_vertex3_mem rev69_vertex2_mem (by decide)
theorem rev69_slab1 (p : Point) (hp : p∈IntegerCarrier rev69_planes)
    (hx0 : rev69_s1_ll.real.1≤p.1) (hx1 : p.1≤rev69_s1_lr.real.1) :
    p∈rationalHull (fractionRow69.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev69_plane26 rev69_plane13 rev69_s1_ll rev69_s1_lr rev69_s1_ul rev69_s1_ur
    (by decide) rev69_s1_ll_mem rev69_s1_lr_mem rev69_s1_ul_mem rev69_s1_ur_mem p
    (hp _ rev69_plane26_mem) (hp _ rev69_plane13_mem) hx0 hx1
def rev69_s2_ll : FractionPoint := ⟨7060476758071777,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev69_s2_ll_mem : rev69_s2_ll.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane73 rev69_vertex1 rev69_vertex2 rev69_s2_ll
    rev69_vertex1_mem rev69_vertex2_mem (by decide)
def rev69_s2_lr : FractionPoint := ⟨6273255497,13928000000,6273255497,13928000000⟩
theorem rev69_s2_lr_mem : rev69_s2_lr.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane73 rev69_vertex1 rev69_vertex2 rev69_s2_lr
    rev69_vertex1_mem rev69_vertex2_mem (by decide)
def rev69_s2_ul : FractionPoint := ⟨7060476758071777,15819173098000000,203241251001744488887,451336827659038000000⟩
theorem rev69_s2_ul_mem : rev69_s2_ul.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane13 rev69_vertex3 rev69_vertex2 rev69_s2_ul
    rev69_vertex3_mem rev69_vertex2_mem (by decide)
def rev69_s2_ur : FractionPoint := ⟨6273255497,13928000000,6273255497,13928000000⟩
theorem rev69_s2_ur_mem : rev69_s2_ur.real ∈ rationalHull (fractionRow69.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow69 rev69_plane13 rev69_vertex3 rev69_vertex2 rev69_s2_ur
    rev69_vertex3_mem rev69_vertex2_mem (by decide)
theorem rev69_slab2 (p : Point) (hp : p∈IntegerCarrier rev69_planes)
    (hx0 : rev69_s2_ll.real.1≤p.1) (hx1 : p.1≤rev69_s2_lr.real.1) :
    p∈rationalHull (fractionRow69.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev69_plane73 rev69_plane13 rev69_s2_ll rev69_s2_lr rev69_s2_ul rev69_s2_ur
    (by decide) rev69_s2_ll_mem rev69_s2_lr_mem rev69_s2_ul_mem rev69_s2_ur_mem p
    (hp _ rev69_plane73_mem) (hp _ rev69_plane13_mem) hx0 hx1
theorem rev69_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev69_planes) : rev69_s0_ll.real.1≤p.1 := by
  have hc := rev69_plane26.combine_sound rev69_plane46 13084000000 2218132000000 (by decide) (by decide) p
    (hp _ rev69_plane26_mem) (hp _ rev69_plane46_mem)
  exact (rev69_plane26.combine rev69_plane46 13084000000 2218132000000).xBoundCheck_sound rev69_s0_ll.nx rev69_s0_ll.dx true (by decide) p hc
theorem rev69_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev69_planes) : p.1≤rev69_s2_lr.real.1 := by
  have hc := rev69_plane13.combine_sound rev69_plane73 51300000000 2168356000000 (by decide) (by decide) p
    (hp _ rev69_plane13_mem) (hp _ rev69_plane73_mem)
  exact (rev69_plane13.combine rev69_plane73 51300000000 2168356000000).xBoundCheck_sound rev69_s2_lr.nx rev69_s2_lr.dx false (by decide) p hc
theorem rev69_hull (p : Point) (hp : p∈IntegerCarrier rev69_planes) :
    p∈rationalHull (fractionRow69.map FractionPoint.rational) := by
  have hxlo := rev69_bound0_lo p hp
  have hxhi := rev69_bound0_hi p hp
  by_cases h0 : p.1≤rev69_s0_lr.real.1
  · exact rev69_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev69_s1_lr.real.1
  · exact rev69_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev69_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull69 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,6,6,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow69 := by
  rw [← fractionRow69_correct]
  exact rev69_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull69
