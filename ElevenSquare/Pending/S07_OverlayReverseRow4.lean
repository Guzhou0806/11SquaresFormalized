import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks0
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev4_planes : List IntegerPlane := integerOverlayPlanes ![0,7,2,0]
def rev4_plane8 : IntegerPlane := ⟨(-15204000000),2139684000000,568962228432⟩
theorem rev4_plane8_mem : rev4_plane8 ∈ rev4_planes := by decide
def rev4_plane47 : IntegerPlane := ⟨(-287616000000),(-1855520000000),(-499376240400)⟩
theorem rev4_plane47_mem : rev4_plane47 ∈ rev4_planes := by decide
def rev4_plane65 : IntegerPlane := ⟨(-699324000000),2145688000000,450639272359⟩
theorem rev4_plane65_mem : rev4_plane65 ∈ rev4_planes := by decide
def rev4_plane69 : IntegerPlane := ⟨1440116000000,2129316000000,827972119784⟩
theorem rev4_plane69_mem : rev4_plane69 ∈ rev4_planes := by decide
def rev4_vertex0 : FractionPoint := fractionRow4[0]!
theorem rev4_vertex0_mem : rev4_vertex0∈fractionRow4 := by decide
def rev4_vertex1 : FractionPoint := fractionRow4[1]!
theorem rev4_vertex1_mem : rev4_vertex1∈fractionRow4 := by decide
def rev4_vertex2 : FractionPoint := fractionRow4[2]!
theorem rev4_vertex2_mem : rev4_vertex2∈fractionRow4 := by decide
def rev4_vertex3 : FractionPoint := fractionRow4[3]!
theorem rev4_vertex3_mem : rev4_vertex3∈fractionRow4 := by decide
def rev4_s0_ll : FractionPoint := ⟨1470846399148897,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev4_s0_ll_mem : rev4_s0_ll.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane47 rev4_vertex2 rev4_vertex3 rev4_s0_ll
    rev4_vertex2_mem rev4_vertex3_mem (by decide)
def rev4_s0_lr : FractionPoint := ⟨4276496419360111,24395155554400000,171130816727793312381,707276547410942000000⟩
theorem rev4_s0_lr_mem : rev4_s0_lr.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane47 rev4_vertex2 rev4_vertex3 rev4_s0_lr
    rev4_vertex2_mem rev4_vertex3_mem (by decide)
def rev4_s0_ul : FractionPoint := ⟨1470846399148897,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev4_s0_ul_mem : rev4_s0_ul.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane65 rev4_vertex2 rev4_vertex1 rev4_s0_ul
    rev4_vertex2_mem rev4_vertex1_mem (by decide)
def rev4_s0_ur : FractionPoint := ⟨4276496419360111,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev4_s0_ur_mem : rev4_s0_ur.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane65 rev4_vertex2 rev4_vertex1 rev4_s0_ur
    rev4_vertex2_mem rev4_vertex1_mem (by decide)
theorem rev4_slab0 (p : Point) (hp : p∈IntegerCarrier rev4_planes)
    (hx0 : rev4_s0_ll.real.1≤p.1) (hx1 : p.1≤rev4_s0_lr.real.1) :
    p∈rationalHull (fractionRow4.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev4_plane47 rev4_plane65 rev4_s0_ll rev4_s0_lr rev4_s0_ul rev4_s0_ur
    (by decide) rev4_s0_ll_mem rev4_s0_lr_mem rev4_s0_ul_mem rev4_s0_ur_mem p
    (hp _ rev4_plane47_mem) (hp _ rev4_plane65_mem) hx0 hx1
def rev4_s1_ll : FractionPoint := ⟨4276496419360111,24395155554400000,171130816727793312381,707276547410942000000⟩
theorem rev4_s1_ll_mem : rev4_s1_ll.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane47 rev4_vertex2 rev4_vertex3 rev4_s1_ll
    rev4_vertex2_mem rev4_vertex3_mem (by decide)
def rev4_s1_lr : FractionPoint := ⟨5834357507833289,32435075873000000,907453229848406788761,3761495748991810000000⟩
theorem rev4_s1_lr_mem : rev4_s1_lr.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane47 rev4_vertex2 rev4_vertex3 rev4_s1_lr
    rev4_vertex2_mem rev4_vertex3_mem (by decide)
def rev4_s1_ul : FractionPoint := ⟨4276496419360111,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev4_s1_ul_mem : rev4_s1_ul.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane8 rev4_vertex1 rev4_vertex0 rev4_s1_ul
    rev4_vertex1_mem rev4_vertex0_mem (by decide)
def rev4_s1_ur : FractionPoint := ⟨5834357507833289,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev4_s1_ur_mem : rev4_s1_ur.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane8 rev4_vertex1 rev4_vertex0 rev4_s1_ur
    rev4_vertex1_mem rev4_vertex0_mem (by decide)
theorem rev4_slab1 (p : Point) (hp : p∈IntegerCarrier rev4_planes)
    (hx0 : rev4_s1_ll.real.1≤p.1) (hx1 : p.1≤rev4_s1_lr.real.1) :
    p∈rationalHull (fractionRow4.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev4_plane47 rev4_plane8 rev4_s1_ll rev4_s1_lr rev4_s1_ul rev4_s1_ur
    (by decide) rev4_s1_ll_mem rev4_s1_lr_mem rev4_s1_ul_mem rev4_s1_ur_mem p
    (hp _ rev4_plane47_mem) (hp _ rev4_plane8_mem) hx0 hx1
def rev4_s2_ll : FractionPoint := ⟨5834357507833289,32435075873000000,907453229848406788761,3761495748991810000000⟩
theorem rev4_s2_ll_mem : rev4_s2_ll.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane47 rev4_vertex2 rev4_vertex3 rev4_s2_ll
    rev4_vertex2_mem rev4_vertex3_mem (by decide)
def rev4_s2_lr : FractionPoint := ⟨1478090653118879,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev4_s2_lr_mem : rev4_s2_lr.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane47 rev4_vertex2 rev4_vertex3 rev4_s2_lr
    rev4_vertex2_mem rev4_vertex3_mem (by decide)
def rev4_s2_ul : FractionPoint := ⟨5834357507833289,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev4_s2_ul_mem : rev4_s2_ul.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane69 rev4_vertex0 rev4_vertex3 rev4_s2_ul
    rev4_vertex0_mem rev4_vertex3_mem (by decide)
def rev4_s2_ur : FractionPoint := ⟨1478090653118879,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev4_s2_ur_mem : rev4_s2_ur.real ∈ rationalHull (fractionRow4.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow4 rev4_plane69 rev4_vertex0 rev4_vertex3 rev4_s2_ur
    rev4_vertex0_mem rev4_vertex3_mem (by decide)
theorem rev4_slab2 (p : Point) (hp : p∈IntegerCarrier rev4_planes)
    (hx0 : rev4_s2_ll.real.1≤p.1) (hx1 : p.1≤rev4_s2_lr.real.1) :
    p∈rationalHull (fractionRow4.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev4_plane47 rev4_plane69 rev4_s2_ll rev4_s2_lr rev4_s2_ul rev4_s2_ur
    (by decide) rev4_s2_ll_mem rev4_s2_lr_mem rev4_s2_ul_mem rev4_s2_ur_mem p
    (hp _ rev4_plane47_mem) (hp _ rev4_plane69_mem) hx0 hx1
theorem rev4_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev4_planes) : rev4_s0_ll.real.1≤p.1 := by
  have hc := rev4_plane47.combine_sound rev4_plane65 2145688000000 1855520000000 (by decide) (by decide) p
    (hp _ rev4_plane47_mem) (hp _ rev4_plane65_mem)
  exact (rev4_plane47.combine rev4_plane65 2145688000000 1855520000000).xBoundCheck_sound rev4_s0_ll.nx rev4_s0_ll.dx true (by decide) p hc
theorem rev4_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev4_planes) : p.1≤rev4_s2_lr.real.1 := by
  have hc := rev4_plane47.combine_sound rev4_plane69 2129316000000 1855520000000 (by decide) (by decide) p
    (hp _ rev4_plane47_mem) (hp _ rev4_plane69_mem)
  exact (rev4_plane47.combine rev4_plane69 2129316000000 1855520000000).xBoundCheck_sound rev4_s2_lr.nx rev4_s2_lr.dx false (by decide) p hc
theorem rev4_hull (p : Point) (hp : p∈IntegerCarrier rev4_planes) :
    p∈rationalHull (fractionRow4.map FractionPoint.rational) := by
  have hxlo := rev4_bound0_lo p hp
  have hxhi := rev4_bound0_hi p hp
  by_cases h0 : p.1≤rev4_s0_lr.real.1
  · exact rev4_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev4_s1_lr.real.1
  · exact rev4_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev4_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull4 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,7,2,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow4 := by
  rw [← fractionRow4_correct]
  exact rev4_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull4
