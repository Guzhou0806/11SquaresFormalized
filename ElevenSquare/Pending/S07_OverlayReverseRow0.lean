import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks0
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev0_planes : List IntegerPlane := integerOverlayPlanes ![0,2,7,0]
def rev0_plane5 : IntegerPlane := ⟨2145688000000,(-699324000000),450639272359⟩
theorem rev0_plane5_mem : rev0_plane5 ∈ rev0_planes := by decide
def rev0_plane9 : IntegerPlane := ⟨2129316000000,1440116000000,827972119784⟩
theorem rev0_plane9_mem : rev0_plane9 ∈ rev0_planes := by decide
def rev0_plane27 : IntegerPlane := ⟨(-1855520000000),(-287616000000),(-499376240400)⟩
theorem rev0_plane27_mem : rev0_plane27 ∈ rev0_planes := by decide
def rev0_plane68 : IntegerPlane := ⟨2139684000000,(-15204000000),568962228432⟩
theorem rev0_plane68_mem : rev0_plane68 ∈ rev0_planes := by decide
def rev0_vertex0 : FractionPoint := fractionRow0[0]!
theorem rev0_vertex0_mem : rev0_vertex0∈fractionRow0 := by decide
def rev0_vertex1 : FractionPoint := fractionRow0[1]!
theorem rev0_vertex1_mem : rev0_vertex1∈fractionRow0 := by decide
def rev0_vertex2 : FractionPoint := fractionRow0[2]!
theorem rev0_vertex2_mem : rev0_vertex2∈fractionRow0 := by decide
def rev0_vertex3 : FractionPoint := fractionRow0[3]!
theorem rev0_vertex3_mem : rev0_vertex3∈fractionRow0 := by decide
def rev0_s0_ll : FractionPoint := ⟨7515963822126429,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev0_s0_ll_mem : rev0_s0_ll.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane27 rev0_vertex3 rev0_vertex0 rev0_s0_ll
    rev0_vertex3_mem rev0_vertex0_mem (by decide)
def rev0_s0_lr : FractionPoint := ⟨2493941952605707,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev0_s0_lr_mem : rev0_s0_lr.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane27 rev0_vertex3 rev0_vertex0 rev0_s0_lr
    rev0_vertex3_mem rev0_vertex0_mem (by decide)
def rev0_s0_ul : FractionPoint := ⟨7515963822126429,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev0_s0_ul_mem : rev0_s0_ul.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane9 rev0_vertex3 rev0_vertex2 rev0_s0_ul
    rev0_vertex3_mem rev0_vertex2_mem (by decide)
def rev0_s0_ur : FractionPoint := ⟨2493941952605707,9972624314000000,736666097579366305441,3590433959145106000000⟩
theorem rev0_s0_ur_mem : rev0_s0_ur.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane9 rev0_vertex3 rev0_vertex2 rev0_s0_ur
    rev0_vertex3_mem rev0_vertex2_mem (by decide)
theorem rev0_slab0 (p : Point) (hp : p∈IntegerCarrier rev0_planes)
    (hx0 : rev0_s0_ll.real.1≤p.1) (hx1 : p.1≤rev0_s0_lr.real.1) :
    p∈rationalHull (fractionRow0.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev0_plane27 rev0_plane9 rev0_s0_ll rev0_s0_lr rev0_s0_ul rev0_s0_ur
    (by decide) rev0_s0_ll_mem rev0_s0_lr_mem rev0_s0_ul_mem rev0_s0_ur_mem p
    (hp _ rev0_plane27_mem) (hp _ rev0_plane9_mem) hx0 hx1
def rev0_s1_ll : FractionPoint := ⟨2493941952605707,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev0_s1_ll_mem : rev0_s1_ll.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane5 rev0_vertex0 rev0_vertex1 rev0_s1_ll
    rev0_vertex0_mem rev0_vertex1_mem (by decide)
def rev0_s1_lr : FractionPoint := ⟨32586451828252811,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev0_s1_lr_mem : rev0_s1_lr.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane5 rev0_vertex0 rev0_vertex1 rev0_s1_lr
    rev0_vertex0_mem rev0_vertex1_mem (by decide)
def rev0_s1_ul : FractionPoint := ⟨2493941952605707,9972624314000000,736666097579366305441,3590433959145106000000⟩
theorem rev0_s1_ul_mem : rev0_s1_ul.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane9 rev0_vertex3 rev0_vertex2 rev0_s1_ul
    rev0_vertex3_mem rev0_vertex2_mem (by decide)
def rev0_s1_ur : FractionPoint := ⟨32586451828252811,121975777772000000,7901422505764246533493,43914817295475388000000⟩
theorem rev0_s1_ur_mem : rev0_s1_ur.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane9 rev0_vertex3 rev0_vertex2 rev0_s1_ur
    rev0_vertex3_mem rev0_vertex2_mem (by decide)
theorem rev0_slab1 (p : Point) (hp : p∈IntegerCarrier rev0_planes)
    (hx0 : rev0_s1_ll.real.1≤p.1) (hx1 : p.1≤rev0_s1_lr.real.1) :
    p∈rationalHull (fractionRow0.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev0_plane5 rev0_plane9 rev0_s1_ll rev0_s1_lr rev0_s1_ul rev0_s1_ur
    (by decide) rev0_s1_ll_mem rev0_s1_lr_mem rev0_s1_ul_mem rev0_s1_ur_mem p
    (hp _ rev0_plane5_mem) (hp _ rev0_plane9_mem) hx0 hx1
def rev0_s2_ll : FractionPoint := ⟨32586451828252811,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev0_s2_ll_mem : rev0_s2_ll.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane68 rev0_vertex1 rev0_vertex2 rev0_s2_ll
    rev0_vertex1_mem rev0_vertex2_mem (by decide)
def rev0_s2_lr : FractionPoint := ⟨8666251006976813,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev0_s2_lr_mem : rev0_s2_lr.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane68 rev0_vertex1 rev0_vertex2 rev0_s2_lr
    rev0_vertex1_mem rev0_vertex2_mem (by decide)
def rev0_s2_ul : FractionPoint := ⟨32586451828252811,121975777772000000,7901422505764246533493,43914817295475388000000⟩
theorem rev0_s2_ul_mem : rev0_s2_ul.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane9 rev0_vertex3 rev0_vertex2 rev0_s2_ul
    rev0_vertex3_mem rev0_vertex2_mem (by decide)
def rev0_s2_ur : FractionPoint := ⟨8666251006976813,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev0_s2_ur_mem : rev0_s2_ur.real ∈ rationalHull (fractionRow0.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow0 rev0_plane9 rev0_vertex3 rev0_vertex2 rev0_s2_ur
    rev0_vertex3_mem rev0_vertex2_mem (by decide)
theorem rev0_slab2 (p : Point) (hp : p∈IntegerCarrier rev0_planes)
    (hx0 : rev0_s2_ll.real.1≤p.1) (hx1 : p.1≤rev0_s2_lr.real.1) :
    p∈rationalHull (fractionRow0.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev0_plane68 rev0_plane9 rev0_s2_ll rev0_s2_lr rev0_s2_ul rev0_s2_ur
    (by decide) rev0_s2_ll_mem rev0_s2_lr_mem rev0_s2_ul_mem rev0_s2_ur_mem p
    (hp _ rev0_plane68_mem) (hp _ rev0_plane9_mem) hx0 hx1
theorem rev0_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev0_planes) : rev0_s0_ll.real.1≤p.1 := by
  have hc := rev0_plane9.combine_sound rev0_plane27 287616000000 1440116000000 (by decide) (by decide) p
    (hp _ rev0_plane9_mem) (hp _ rev0_plane27_mem)
  exact (rev0_plane9.combine rev0_plane27 287616000000 1440116000000).xBoundCheck_sound rev0_s0_ll.nx rev0_s0_ll.dx true (by decide) p hc
theorem rev0_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev0_planes) : p.1≤rev0_s2_lr.real.1 := by
  have hc := rev0_plane9.combine_sound rev0_plane68 15204000000 1440116000000 (by decide) (by decide) p
    (hp _ rev0_plane9_mem) (hp _ rev0_plane68_mem)
  exact (rev0_plane9.combine rev0_plane68 15204000000 1440116000000).xBoundCheck_sound rev0_s2_lr.nx rev0_s2_lr.dx false (by decide) p hc
theorem rev0_hull (p : Point) (hp : p∈IntegerCarrier rev0_planes) :
    p∈rationalHull (fractionRow0.map FractionPoint.rational) := by
  have hxlo := rev0_bound0_lo p hp
  have hxhi := rev0_bound0_hi p hp
  by_cases h0 : p.1≤rev0_s0_lr.real.1
  · exact rev0_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev0_s1_lr.real.1
  · exact rev0_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev0_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull0 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,2,7,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow0 := by
  rw [← fractionRow0_correct]
  exact rev0_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull0
