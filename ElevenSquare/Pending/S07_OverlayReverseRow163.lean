import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks20
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev163_planes : List IntegerPlane := integerOverlayPlanes ![10,13,9,10]
def rev163_plane33 : IntegerPlane := ⟨13084000000,(-2218132000000),(-1594545024972)⟩
theorem rev163_plane33_mem : rev163_plane33 ∈ rev163_planes := by decide
def rev163_plane52 : IntegerPlane := ⟨643972000000,2044968000000,1962432524019⟩
theorem rev163_plane52_mem : rev163_plane52 ∈ rev163_planes := by decide
def rev163_plane57 : IntegerPlane := ⟨2218132000000,(-13084000000),1594545024972⟩
theorem rev163_plane57_mem : rev163_plane57 ∈ rev163_planes := by decide
def rev163_plane70 : IntegerPlane := ⟨(-2168356000000),51300000000,(-1163521164456)⟩
theorem rev163_plane70_mem : rev163_plane70 ∈ rev163_planes := by decide
def rev163_plane75 : IntegerPlane := ⟨(-699568000000),2144520000000,1185942108648⟩
theorem rev163_plane75_mem : rev163_plane75 ∈ rev163_planes := by decide
def rev163_vertex0 : FractionPoint := fractionRow163[0]!
theorem rev163_vertex0_mem : rev163_vertex0∈fractionRow163 := by decide
def rev163_vertex1 : FractionPoint := fractionRow163[1]!
theorem rev163_vertex1_mem : rev163_vertex1∈fractionRow163 := by decide
def rev163_vertex2 : FractionPoint := fractionRow163[2]!
theorem rev163_vertex2_mem : rev163_vertex2∈fractionRow163 := by decide
def rev163_vertex3 : FractionPoint := fractionRow163[3]!
theorem rev163_vertex3_mem : rev163_vertex3∈fractionRow163 := by decide
def rev163_vertex4 : FractionPoint := fractionRow163[4]!
theorem rev163_vertex4_mem : rev163_vertex4∈fractionRow163 := by decide
def rev163_s0_ll : FractionPoint := ⟨8758696339928223,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev163_s0_ll_mem : rev163_s0_ll.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane33 rev163_vertex0 rev163_vertex1 rev163_s0_ll
    rev163_vertex0_mem rev163_vertex1_mem (by decide)
def rev163_s0_lr : FractionPoint := ⟨4061837715759,7332499000000,1468143110716894473,2033056333983500000⟩
theorem rev163_s0_lr_mem : rev163_s0_lr.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane33 rev163_vertex0 rev163_vertex1 rev163_s0_lr
    rev163_vertex0_mem rev163_vertex1_mem (by decide)
def rev163_s0_ul : FractionPoint := ⟨8758696339928223,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev163_s0_ul_mem : rev163_s0_ul.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane70 rev163_vertex0 rev163_vertex4 rev163_s0_ul
    rev163_vertex0_mem rev163_vertex4_mem (by decide)
def rev163_s0_ur : FractionPoint := ⟨4061837715759,7332499000000,80699534251423,109987485000000⟩
theorem rev163_s0_ur_mem : rev163_s0_ur.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane70 rev163_vertex0 rev163_vertex4 rev163_s0_ur
    rev163_vertex0_mem rev163_vertex4_mem (by decide)
theorem rev163_slab0 (p : Point) (hp : p∈IntegerCarrier rev163_planes)
    (hx0 : rev163_s0_ll.real.1≤p.1) (hx1 : p.1≤rev163_s0_lr.real.1) :
    p∈rationalHull (fractionRow163.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev163_plane33 rev163_plane70 rev163_s0_ll rev163_s0_lr rev163_s0_ul rev163_s0_ur
    (by decide) rev163_s0_ll_mem rev163_s0_lr_mem rev163_s0_ul_mem rev163_s0_ur_mem p
    (hp _ rev163_plane33_mem) (hp _ rev163_plane70_mem) hx0 hx1
def rev163_s1_ll : FractionPoint := ⟨4061837715759,7332499000000,1468143110716894473,2033056333983500000⟩
theorem rev163_s1_ll_mem : rev163_s1_ll.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane33 rev163_vertex0 rev163_vertex1 rev163_s1_ll
    rev163_vertex0_mem rev163_vertex1_mem (by decide)
def rev163_s1_lr : FractionPoint := ⟨3230547344875983,5093487332000000,2041015841614715754069,2824506810675956000000⟩
theorem rev163_s1_lr_mem : rev163_s1_lr.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane33 rev163_vertex0 rev163_vertex1 rev163_s1_lr
    rev163_vertex0_mem rev163_vertex1_mem (by decide)
def rev163_s1_ul : FractionPoint := ⟨4061837715759,7332499000000,80699534251423,109987485000000⟩
theorem rev163_s1_ul_mem : rev163_s1_ul.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane75 rev163_vertex4 rev163_vertex3 rev163_s1_ul
    rev163_vertex4_mem rev163_vertex3_mem (by decide)
def rev163_s1_ur : FractionPoint := ⟨3230547344875983,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev163_s1_ur_mem : rev163_s1_ur.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane75 rev163_vertex4 rev163_vertex3 rev163_s1_ur
    rev163_vertex4_mem rev163_vertex3_mem (by decide)
theorem rev163_slab1 (p : Point) (hp : p∈IntegerCarrier rev163_planes)
    (hx0 : rev163_s1_ll.real.1≤p.1) (hx1 : p.1≤rev163_s1_lr.real.1) :
    p∈rationalHull (fractionRow163.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev163_plane33 rev163_plane75 rev163_s1_ll rev163_s1_lr rev163_s1_ul rev163_s1_ur
    (by decide) rev163_s1_ll_mem rev163_s1_lr_mem rev163_s1_ul_mem rev163_s1_ur_mem p
    (hp _ rev163_plane33_mem) (hp _ rev163_plane75_mem) hx0 hx1
def rev163_s2_ll : FractionPoint := ⟨3230547344875983,5093487332000000,2041015841614715754069,2824506810675956000000⟩
theorem rev163_s2_ll_mem : rev163_s2_ll.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane33 rev163_vertex0 rev163_vertex1 rev163_s2_ll
    rev163_vertex0_mem rev163_vertex1_mem (by decide)
def rev163_s2_lr : FractionPoint := ⟨132878752081,183754000000,132878752081,183754000000⟩
theorem rev163_s2_lr_mem : rev163_s2_lr.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane33 rev163_vertex0 rev163_vertex1 rev163_s2_lr
    rev163_vertex0_mem rev163_vertex1_mem (by decide)
def rev163_s2_ul : FractionPoint := ⟨3230547344875983,5093487332000000,1935297561189487,2546743666000000⟩
theorem rev163_s2_ul_mem : rev163_s2_ul.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane52 rev163_vertex3 rev163_vertex2 rev163_s2_ul
    rev163_vertex3_mem rev163_vertex2_mem (by decide)
def rev163_s2_ur : FractionPoint := ⟨132878752081,183754000000,137517315141740797,187885524936000000⟩
theorem rev163_s2_ur_mem : rev163_s2_ur.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane52 rev163_vertex3 rev163_vertex2 rev163_s2_ur
    rev163_vertex3_mem rev163_vertex2_mem (by decide)
theorem rev163_slab2 (p : Point) (hp : p∈IntegerCarrier rev163_planes)
    (hx0 : rev163_s2_ll.real.1≤p.1) (hx1 : p.1≤rev163_s2_lr.real.1) :
    p∈rationalHull (fractionRow163.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev163_plane33 rev163_plane52 rev163_s2_ll rev163_s2_lr rev163_s2_ul rev163_s2_ur
    (by decide) rev163_s2_ll_mem rev163_s2_lr_mem rev163_s2_ul_mem rev163_s2_ur_mem p
    (hp _ rev163_plane33_mem) (hp _ rev163_plane52_mem) hx0 hx1
def rev163_s3_ll : FractionPoint := ⟨132878752081,183754000000,132878752081,183754000000⟩
theorem rev163_s3_ll_mem : rev163_s3_ll.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane57 rev163_vertex1 rev163_vertex2 rev163_s3_ll
    rev163_vertex1_mem rev163_vertex2_mem (by decide)
def rev163_s3_lr : FractionPoint := ⟨821617504442801373,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev163_s3_lr_mem : rev163_s3_lr.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane57 rev163_vertex1 rev163_vertex2 rev163_s3_lr
    rev163_vertex1_mem rev163_vertex2_mem (by decide)
def rev163_s3_ul : FractionPoint := ⟨132878752081,183754000000,137517315141740797,187885524936000000⟩
theorem rev163_s3_ul_mem : rev163_s3_ul.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane52 rev163_vertex3 rev163_vertex2 rev163_s3_ul
    rev163_vertex3_mem rev163_vertex2_mem (by decide)
def rev163_s3_ur : FractionPoint := ⟨821617504442801373,1136108672356000000,118789001090930133,162301238908000000⟩
theorem rev163_s3_ur_mem : rev163_s3_ur.real ∈ rationalHull (fractionRow163.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow163 rev163_plane52 rev163_vertex3 rev163_vertex2 rev163_s3_ur
    rev163_vertex3_mem rev163_vertex2_mem (by decide)
theorem rev163_slab3 (p : Point) (hp : p∈IntegerCarrier rev163_planes)
    (hx0 : rev163_s3_ll.real.1≤p.1) (hx1 : p.1≤rev163_s3_lr.real.1) :
    p∈rationalHull (fractionRow163.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev163_plane57 rev163_plane52 rev163_s3_ll rev163_s3_lr rev163_s3_ul rev163_s3_ur
    (by decide) rev163_s3_ll_mem rev163_s3_lr_mem rev163_s3_ul_mem rev163_s3_ur_mem p
    (hp _ rev163_plane57_mem) (hp _ rev163_plane52_mem) hx0 hx1
theorem rev163_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev163_planes) : rev163_s0_ll.real.1≤p.1 := by
  have hc := rev163_plane33.combine_sound rev163_plane70 51300000000 2218132000000 (by decide) (by decide) p
    (hp _ rev163_plane33_mem) (hp _ rev163_plane70_mem)
  exact (rev163_plane33.combine rev163_plane70 51300000000 2218132000000).xBoundCheck_sound rev163_s0_ll.nx rev163_s0_ll.dx true (by decide) p hc
theorem rev163_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev163_planes) : p.1≤rev163_s3_lr.real.1 := by
  have hc := rev163_plane52.combine_sound rev163_plane57 13084000000 2044968000000 (by decide) (by decide) p
    (hp _ rev163_plane52_mem) (hp _ rev163_plane57_mem)
  exact (rev163_plane52.combine rev163_plane57 13084000000 2044968000000).xBoundCheck_sound rev163_s3_lr.nx rev163_s3_lr.dx false (by decide) p hc
theorem rev163_hull (p : Point) (hp : p∈IntegerCarrier rev163_planes) :
    p∈rationalHull (fractionRow163.map FractionPoint.rational) := by
  have hxlo := rev163_bound0_lo p hp
  have hxhi := rev163_bound0_hi p hp
  by_cases h0 : p.1≤rev163_s0_lr.real.1
  · exact rev163_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev163_s1_lr.real.1
  · exact rev163_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev163_s2_lr.real.1
  · exact rev163_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev163_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull163 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,13,9,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow163 := by
  rw [← fractionRow163_correct]
  exact rev163_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull163
