import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks24
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev198_planes : List IntegerPlane := integerOverlayPlanes ![13,15,0,7]
def rev198_plane16 : IntegerPlane := ⟨(-1855520000000),287616000000,(-211760240400)⟩
theorem rev198_plane16_mem : rev198_plane16 ∈ rev198_planes := by decide
def rev198_plane34 : IntegerPlane := ⟨2129316000000,(-1440116000000),(-612143880216)⟩
theorem rev198_plane34_mem : rev198_plane34 ∈ rev198_planes := by decide
def rev198_plane38 : IntegerPlane := ⟨2145688000000,699324000000,1149963272359⟩
theorem rev198_plane38_mem : rev198_plane38 ∈ rev198_planes := by decide
def rev198_plane48 : IntegerPlane := ⟨2139684000000,15204000000,584166228432⟩
theorem rev198_plane48_mem : rev198_plane48 ∈ rev198_planes := by decide
def rev198_vertex0 : FractionPoint := fractionRow198[0]!
theorem rev198_vertex0_mem : rev198_vertex0∈fractionRow198 := by decide
def rev198_vertex1 : FractionPoint := fractionRow198[1]!
theorem rev198_vertex1_mem : rev198_vertex1∈fractionRow198 := by decide
def rev198_vertex2 : FractionPoint := fractionRow198[2]!
theorem rev198_vertex2_mem : rev198_vertex2∈fractionRow198 := by decide
def rev198_vertex3 : FractionPoint := fractionRow198[3]!
theorem rev198_vertex3_mem : rev198_vertex3∈fractionRow198 := by decide
def rev198_s0_ll : FractionPoint := ⟨7515963822126429,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev198_s0_ll_mem : rev198_s0_ll.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane34 rev198_vertex1 rev198_vertex2 rev198_s0_ll
    rev198_vertex1_mem rev198_vertex2_mem (by decide)
def rev198_s0_lr : FractionPoint := ⟨2493941952605707,9972624314000000,2853767861565739694559,3590433959145106000000⟩
theorem rev198_s0_lr_mem : rev198_s0_lr.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane34 rev198_vertex1 rev198_vertex2 rev198_s0_lr
    rev198_vertex1_mem rev198_vertex2_mem (by decide)
def rev198_s0_ul : FractionPoint := ⟨7515963822126429,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev198_s0_ul_mem : rev198_s0_ul.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane16 rev198_vertex1 rev198_vertex0 rev198_s0_ul
    rev198_vertex1_mem rev198_vertex0_mem (by decide)
def rev198_s0_ur : FractionPoint := ⟨2493941952605707,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev198_s0_ur_mem : rev198_s0_ur.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane16 rev198_vertex1 rev198_vertex0 rev198_s0_ur
    rev198_vertex1_mem rev198_vertex0_mem (by decide)
theorem rev198_slab0 (p : Point) (hp : p∈IntegerCarrier rev198_planes)
    (hx0 : rev198_s0_ll.real.1≤p.1) (hx1 : p.1≤rev198_s0_lr.real.1) :
    p∈rationalHull (fractionRow198.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev198_plane34 rev198_plane16 rev198_s0_ll rev198_s0_lr rev198_s0_ul rev198_s0_ur
    (by decide) rev198_s0_ll_mem rev198_s0_lr_mem rev198_s0_ul_mem rev198_s0_ur_mem p
    (hp _ rev198_plane34_mem) (hp _ rev198_plane16_mem) hx0 hx1
def rev198_s1_ll : FractionPoint := ⟨2493941952605707,9972624314000000,2853767861565739694559,3590433959145106000000⟩
theorem rev198_s1_ll_mem : rev198_s1_ll.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane34 rev198_vertex1 rev198_vertex2 rev198_s1_ll
    rev198_vertex1_mem rev198_vertex2_mem (by decide)
def rev198_s1_lr : FractionPoint := ⟨32586451828252811,121975777772000000,36013394789711141466507,43914817295475388000000⟩
theorem rev198_s1_lr_mem : rev198_s1_lr.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane34 rev198_vertex1 rev198_vertex2 rev198_s1_lr
    rev198_vertex1_mem rev198_vertex2_mem (by decide)
def rev198_s1_ul : FractionPoint := ⟨2493941952605707,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev198_s1_ul_mem : rev198_s1_ul.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane38 rev198_vertex0 rev198_vertex3 rev198_s1_ul
    rev198_vertex0_mem rev198_vertex3_mem (by decide)
def rev198_s1_ur : FractionPoint := ⟨32586451828252811,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev198_s1_ur_mem : rev198_s1_ur.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane38 rev198_vertex0 rev198_vertex3 rev198_s1_ur
    rev198_vertex0_mem rev198_vertex3_mem (by decide)
theorem rev198_slab1 (p : Point) (hp : p∈IntegerCarrier rev198_planes)
    (hx0 : rev198_s1_ll.real.1≤p.1) (hx1 : p.1≤rev198_s1_lr.real.1) :
    p∈rationalHull (fractionRow198.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev198_plane34 rev198_plane38 rev198_s1_ll rev198_s1_lr rev198_s1_ul rev198_s1_ur
    (by decide) rev198_s1_ll_mem rev198_s1_lr_mem rev198_s1_ul_mem rev198_s1_ur_mem p
    (hp _ rev198_plane34_mem) (hp _ rev198_plane38_mem) hx0 hx1
def rev198_s2_ll : FractionPoint := ⟨32586451828252811,121975777772000000,36013394789711141466507,43914817295475388000000⟩
theorem rev198_s2_ll_mem : rev198_s2_ll.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane34 rev198_vertex1 rev198_vertex2 rev198_s2_ll
    rev198_vertex1_mem rev198_vertex2_mem (by decide)
def rev198_s2_lr : FractionPoint := ⟨8666251006976813,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev198_s2_lr_mem : rev198_s2_lr.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane34 rev198_vertex1 rev198_vertex2 rev198_s2_lr
    rev198_vertex1_mem rev198_vertex2_mem (by decide)
def rev198_s2_ul : FractionPoint := ⟨32586451828252811,121975777772000000,20118659135039889,24395155554400000⟩
theorem rev198_s2_ul_mem : rev198_s2_ul.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane48 rev198_vertex3 rev198_vertex2 rev198_s2_ul
    rev198_vertex3_mem rev198_vertex2_mem (by decide)
def rev198_s2_ur : FractionPoint := ⟨8666251006976813,32435075873000000,26600718365166711,32435075873000000⟩
theorem rev198_s2_ur_mem : rev198_s2_ur.real ∈ rationalHull (fractionRow198.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow198 rev198_plane48 rev198_vertex3 rev198_vertex2 rev198_s2_ur
    rev198_vertex3_mem rev198_vertex2_mem (by decide)
theorem rev198_slab2 (p : Point) (hp : p∈IntegerCarrier rev198_planes)
    (hx0 : rev198_s2_ll.real.1≤p.1) (hx1 : p.1≤rev198_s2_lr.real.1) :
    p∈rationalHull (fractionRow198.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev198_plane34 rev198_plane48 rev198_s2_ll rev198_s2_lr rev198_s2_ul rev198_s2_ur
    (by decide) rev198_s2_ll_mem rev198_s2_lr_mem rev198_s2_ul_mem rev198_s2_ur_mem p
    (hp _ rev198_plane34_mem) (hp _ rev198_plane48_mem) hx0 hx1
theorem rev198_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev198_planes) : rev198_s0_ll.real.1≤p.1 := by
  have hc := rev198_plane16.combine_sound rev198_plane34 1440116000000 287616000000 (by decide) (by decide) p
    (hp _ rev198_plane16_mem) (hp _ rev198_plane34_mem)
  exact (rev198_plane16.combine rev198_plane34 1440116000000 287616000000).xBoundCheck_sound rev198_s0_ll.nx rev198_s0_ll.dx true (by decide) p hc
theorem rev198_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev198_planes) : p.1≤rev198_s2_lr.real.1 := by
  have hc := rev198_plane34.combine_sound rev198_plane48 15204000000 1440116000000 (by decide) (by decide) p
    (hp _ rev198_plane34_mem) (hp _ rev198_plane48_mem)
  exact (rev198_plane34.combine rev198_plane48 15204000000 1440116000000).xBoundCheck_sound rev198_s2_lr.nx rev198_s2_lr.dx false (by decide) p hc
theorem rev198_hull (p : Point) (hp : p∈IntegerCarrier rev198_planes) :
    p∈rationalHull (fractionRow198.map FractionPoint.rational) := by
  have hxlo := rev198_bound0_lo p hp
  have hxhi := rev198_bound0_hi p hp
  by_cases h0 : p.1≤rev198_s0_lr.real.1
  · exact rev198_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev198_s1_lr.real.1
  · exact rev198_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev198_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull198 (p : Point)
    (hp : ∀ g, ClosedCell ((![13,15,0,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow198 := by
  rw [← fractionRow198_correct]
  exact rev198_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull198
