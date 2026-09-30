import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks1
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev15_planes : List IntegerPlane := integerOverlayPlanes ![1,2,7,0]
def rev15_plane4 : IntegerPlane := ⟨(-2145688000000),699324000000,(-450639272359)⟩
theorem rev15_plane4_mem : rev15_plane4 ∈ rev15_planes := by decide
def rev15_plane27 : IntegerPlane := ⟨(-1855520000000),(-287616000000),(-499376240400)⟩
theorem rev15_plane27_mem : rev15_plane27 ∈ rev15_planes := by decide
def rev15_plane68 : IntegerPlane := ⟨2139684000000,(-15204000000),568962228432⟩
theorem rev15_plane68_mem : rev15_plane68 ∈ rev15_planes := by decide
def rev15_vertex0 : FractionPoint := fractionRow15[0]!
theorem rev15_vertex0_mem : rev15_vertex0∈fractionRow15 := by decide
def rev15_vertex1 : FractionPoint := fractionRow15[1]!
theorem rev15_vertex1_mem : rev15_vertex1∈fractionRow15 := by decide
def rev15_vertex2 : FractionPoint := fractionRow15[2]!
theorem rev15_vertex2_mem : rev15_vertex2∈fractionRow15 := by decide
def rev15_s0_ll : FractionPoint := ⟨2493941952605707,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev15_s0_ll_mem : rev15_s0_ll.real ∈ rationalHull (fractionRow15.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow15 rev15_plane27 rev15_vertex1 rev15_vertex2 rev15_s0_ll
    rev15_vertex1_mem rev15_vertex2_mem (by decide)
def rev15_s0_lr : FractionPoint := ⟨127407110603973,478882946000000,13319330691551,670436124400000⟩
theorem rev15_s0_lr_mem : rev15_s0_lr.real ∈ rationalHull (fractionRow15.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow15 rev15_plane27 rev15_vertex1 rev15_vertex2 rev15_s0_lr
    rev15_vertex1_mem rev15_vertex2_mem (by decide)
def rev15_s0_ul : FractionPoint := ⟨2493941952605707,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev15_s0_ul_mem : rev15_s0_ul.real ∈ rationalHull (fractionRow15.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow15 rev15_plane4 rev15_vertex1 rev15_vertex0 rev15_s0_ul
    rev15_vertex1_mem rev15_vertex0_mem (by decide)
def rev15_s0_ur : FractionPoint := ⟨127407110603973,478882946000000,5757244600704332881,33489433732850400000⟩
theorem rev15_s0_ur_mem : rev15_s0_ur.real ∈ rationalHull (fractionRow15.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow15 rev15_plane4 rev15_vertex1 rev15_vertex0 rev15_s0_ur
    rev15_vertex1_mem rev15_vertex0_mem (by decide)
theorem rev15_slab0 (p : Point) (hp : p∈IntegerCarrier rev15_planes)
    (hx0 : rev15_s0_ll.real.1≤p.1) (hx1 : p.1≤rev15_s0_lr.real.1) :
    p∈rationalHull (fractionRow15.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev15_plane27 rev15_plane4 rev15_s0_ll rev15_s0_lr rev15_s0_ul rev15_s0_ur
    (by decide) rev15_s0_ll_mem rev15_s0_lr_mem rev15_s0_ul_mem rev15_s0_ur_mem p
    (hp _ rev15_plane27_mem) (hp _ rev15_plane4_mem) hx0 hx1
def rev15_s1_ll : FractionPoint := ⟨127407110603973,478882946000000,13319330691551,670436124400000⟩
theorem rev15_s1_ll_mem : rev15_s1_ll.real ∈ rationalHull (fractionRow15.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow15 rev15_plane68 rev15_vertex2 rev15_vertex0 rev15_s1_ll
    rev15_vertex2_mem rev15_vertex0_mem (by decide)
def rev15_s1_lr : FractionPoint := ⟨32586451828252811,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev15_s1_lr_mem : rev15_s1_lr.real ∈ rationalHull (fractionRow15.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow15 rev15_plane68 rev15_vertex2 rev15_vertex0 rev15_s1_lr
    rev15_vertex2_mem rev15_vertex0_mem (by decide)
def rev15_s1_ul : FractionPoint := ⟨127407110603973,478882946000000,5757244600704332881,33489433732850400000⟩
theorem rev15_s1_ul_mem : rev15_s1_ul.real ∈ rationalHull (fractionRow15.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow15 rev15_plane4 rev15_vertex1 rev15_vertex0 rev15_s1_ul
    rev15_vertex1_mem rev15_vertex0_mem (by decide)
def rev15_s1_ur : FractionPoint := ⟨32586451828252811,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev15_s1_ur_mem : rev15_s1_ur.real ∈ rationalHull (fractionRow15.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow15 rev15_plane4 rev15_vertex1 rev15_vertex0 rev15_s1_ur
    rev15_vertex1_mem rev15_vertex0_mem (by decide)
theorem rev15_slab1 (p : Point) (hp : p∈IntegerCarrier rev15_planes)
    (hx0 : rev15_s1_ll.real.1≤p.1) (hx1 : p.1≤rev15_s1_lr.real.1) :
    p∈rationalHull (fractionRow15.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev15_plane68 rev15_plane4 rev15_s1_ll rev15_s1_lr rev15_s1_ul rev15_s1_ur
    (by decide) rev15_s1_ll_mem rev15_s1_lr_mem rev15_s1_ul_mem rev15_s1_ur_mem p
    (hp _ rev15_plane68_mem) (hp _ rev15_plane4_mem) hx0 hx1
theorem rev15_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev15_planes) : rev15_s0_ll.real.1≤p.1 := by
  have hc := rev15_plane4.combine_sound rev15_plane27 287616000000 699324000000 (by decide) (by decide) p
    (hp _ rev15_plane4_mem) (hp _ rev15_plane27_mem)
  exact (rev15_plane4.combine rev15_plane27 287616000000 699324000000).xBoundCheck_sound rev15_s0_ll.nx rev15_s0_ll.dx true (by decide) p hc
theorem rev15_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev15_planes) : p.1≤rev15_s1_lr.real.1 := by
  have hc := rev15_plane4.combine_sound rev15_plane68 15204000000 699324000000 (by decide) (by decide) p
    (hp _ rev15_plane4_mem) (hp _ rev15_plane68_mem)
  exact (rev15_plane4.combine rev15_plane68 15204000000 699324000000).xBoundCheck_sound rev15_s1_lr.nx rev15_s1_lr.dx false (by decide) p hc
theorem rev15_hull (p : Point) (hp : p∈IntegerCarrier rev15_planes) :
    p∈rationalHull (fractionRow15.map FractionPoint.rational) := by
  have hxlo := rev15_bound0_lo p hp
  have hxhi := rev15_bound0_hi p hp
  by_cases h0 : p.1≤rev15_s0_lr.real.1
  · exact rev15_slab0 p hp hxlo h0
  exact rev15_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull15 (p : Point)
    (hp : ∀ g, ClosedCell ((![1,2,7,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow15 := by
  rw [← fractionRow15_correct]
  exact rev15_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull15
