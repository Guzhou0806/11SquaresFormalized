import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks12
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev100_planes : List IntegerPlane := integerOverlayPlanes ![7,0,15,13]
def rev100_plane28 : IntegerPlane := ⟨15204000000,2139684000000,584166228432⟩
theorem rev100_plane28_mem : rev100_plane28 ∈ rev100_planes := by decide
def rev100_plane54 : IntegerPlane := ⟨(-1440116000000),2129316000000,(-612143880216)⟩
theorem rev100_plane54_mem : rev100_plane54 ∈ rev100_planes := by decide
def rev100_plane58 : IntegerPlane := ⟨699324000000,2145688000000,1149963272359⟩
theorem rev100_plane58_mem : rev100_plane58 ∈ rev100_planes := by decide
def rev100_plane76 : IntegerPlane := ⟨287616000000,(-1855520000000),(-211760240400)⟩
theorem rev100_plane76_mem : rev100_plane76 ∈ rev100_planes := by decide
def rev100_vertex0 : FractionPoint := fractionRow100[0]!
theorem rev100_vertex0_mem : rev100_vertex0∈fractionRow100 := by decide
def rev100_vertex1 : FractionPoint := fractionRow100[1]!
theorem rev100_vertex1_mem : rev100_vertex1∈fractionRow100 := by decide
def rev100_vertex2 : FractionPoint := fractionRow100[2]!
theorem rev100_vertex2_mem : rev100_vertex2∈fractionRow100 := by decide
def rev100_vertex3 : FractionPoint := fractionRow100[3]!
theorem rev100_vertex3_mem : rev100_vertex3∈fractionRow100 := by decide
def rev100_s0_ll : FractionPoint := ⟨4958592752081121,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev100_s0_ll_mem : rev100_s0_ll.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane76 rev100_vertex3 rev100_vertex0 rev100_s0_ll
    rev100_vertex3_mem rev100_vertex0_mem (by decide)
def rev100_s0_lr : FractionPoint := ⟨26600718365166711,32435075873000000,907453229848406788761,3761495748991810000000⟩
theorem rev100_s0_lr_mem : rev100_s0_lr.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane76 rev100_vertex3 rev100_vertex0 rev100_s0_lr
    rev100_vertex3_mem rev100_vertex0_mem (by decide)
def rev100_s0_ul : FractionPoint := ⟨4958592752081121,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev100_s0_ul_mem : rev100_s0_ul.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane54 rev100_vertex3 rev100_vertex2 rev100_s0_ul
    rev100_vertex3_mem rev100_vertex2_mem (by decide)
def rev100_s0_ur : FractionPoint := ⟨26600718365166711,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev100_s0_ur_mem : rev100_s0_ur.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane54 rev100_vertex3 rev100_vertex2 rev100_s0_ur
    rev100_vertex3_mem rev100_vertex2_mem (by decide)
theorem rev100_slab0 (p : Point) (hp : p∈IntegerCarrier rev100_planes)
    (hx0 : rev100_s0_ll.real.1≤p.1) (hx1 : p.1≤rev100_s0_lr.real.1) :
    p∈rationalHull (fractionRow100.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev100_plane76 rev100_plane54 rev100_s0_ll rev100_s0_lr rev100_s0_ul rev100_s0_ur
    (by decide) rev100_s0_ll_mem rev100_s0_lr_mem rev100_s0_ul_mem rev100_s0_ur_mem p
    (hp _ rev100_plane76_mem) (hp _ rev100_plane54_mem) hx0 hx1
def rev100_s1_ll : FractionPoint := ⟨26600718365166711,32435075873000000,907453229848406788761,3761495748991810000000⟩
theorem rev100_s1_ll_mem : rev100_s1_ll.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane76 rev100_vertex3 rev100_vertex0 rev100_s1_ll
    rev100_vertex3_mem rev100_vertex0_mem (by decide)
def rev100_s1_lr : FractionPoint := ⟨20118659135039889,24395155554400000,171130816727793312381,707276547410942000000⟩
theorem rev100_s1_lr_mem : rev100_s1_lr.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane76 rev100_vertex3 rev100_vertex0 rev100_s1_lr
    rev100_vertex3_mem rev100_vertex0_mem (by decide)
def rev100_s1_ul : FractionPoint := ⟨26600718365166711,32435075873000000,8666251006976813,32435075873000000⟩
theorem rev100_s1_ul_mem : rev100_s1_ul.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane28 rev100_vertex2 rev100_vertex1 rev100_s1_ul
    rev100_vertex2_mem rev100_vertex1_mem (by decide)
def rev100_s1_ur : FractionPoint := ⟨20118659135039889,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev100_s1_ur_mem : rev100_s1_ur.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane28 rev100_vertex2 rev100_vertex1 rev100_s1_ur
    rev100_vertex2_mem rev100_vertex1_mem (by decide)
theorem rev100_slab1 (p : Point) (hp : p∈IntegerCarrier rev100_planes)
    (hx0 : rev100_s1_ll.real.1≤p.1) (hx1 : p.1≤rev100_s1_lr.real.1) :
    p∈rationalHull (fractionRow100.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev100_plane76 rev100_plane28 rev100_s1_ll rev100_s1_lr rev100_s1_ul rev100_s1_ur
    (by decide) rev100_s1_ll_mem rev100_s1_lr_mem rev100_s1_ul_mem rev100_s1_ur_mem p
    (hp _ rev100_plane76_mem) (hp _ rev100_plane28_mem) hx0 hx1
def rev100_s2_ll : FractionPoint := ⟨20118659135039889,24395155554400000,171130816727793312381,707276547410942000000⟩
theorem rev100_s2_ll_mem : rev100_s2_ll.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane76 rev100_vertex3 rev100_vertex0 rev100_s2_ll
    rev100_vertex3_mem rev100_vertex0_mem (by decide)
def rev100_s2_lr : FractionPoint := ⟨10496302777651103,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev100_s2_lr_mem : rev100_s2_lr.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane76 rev100_vertex3 rev100_vertex0 rev100_s2_lr
    rev100_vertex3_mem rev100_vertex0_mem (by decide)
def rev100_s2_ul : FractionPoint := ⟨20118659135039889,24395155554400000,32586451828252811,121975777772000000⟩
theorem rev100_s2_ul_mem : rev100_s2_ul.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane58 rev100_vertex1 rev100_vertex0 rev100_s2_ul
    rev100_vertex1_mem rev100_vertex0_mem (by decide)
def rev100_s2_ur : FractionPoint := ⟨10496302777651103,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev100_s2_ur_mem : rev100_s2_ur.real ∈ rationalHull (fractionRow100.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow100 rev100_plane58 rev100_vertex1 rev100_vertex0 rev100_s2_ur
    rev100_vertex1_mem rev100_vertex0_mem (by decide)
theorem rev100_slab2 (p : Point) (hp : p∈IntegerCarrier rev100_planes)
    (hx0 : rev100_s2_ll.real.1≤p.1) (hx1 : p.1≤rev100_s2_lr.real.1) :
    p∈rationalHull (fractionRow100.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev100_plane76 rev100_plane58 rev100_s2_ll rev100_s2_lr rev100_s2_ul rev100_s2_ur
    (by decide) rev100_s2_ll_mem rev100_s2_lr_mem rev100_s2_ul_mem rev100_s2_ur_mem p
    (hp _ rev100_plane76_mem) (hp _ rev100_plane58_mem) hx0 hx1
theorem rev100_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev100_planes) : rev100_s0_ll.real.1≤p.1 := by
  have hc := rev100_plane54.combine_sound rev100_plane76 1855520000000 2129316000000 (by decide) (by decide) p
    (hp _ rev100_plane54_mem) (hp _ rev100_plane76_mem)
  exact (rev100_plane54.combine rev100_plane76 1855520000000 2129316000000).xBoundCheck_sound rev100_s0_ll.nx rev100_s0_ll.dx true (by decide) p hc
theorem rev100_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev100_planes) : p.1≤rev100_s2_lr.real.1 := by
  have hc := rev100_plane58.combine_sound rev100_plane76 1855520000000 2145688000000 (by decide) (by decide) p
    (hp _ rev100_plane58_mem) (hp _ rev100_plane76_mem)
  exact (rev100_plane58.combine rev100_plane76 1855520000000 2145688000000).xBoundCheck_sound rev100_s2_lr.nx rev100_s2_lr.dx false (by decide) p hc
theorem rev100_hull (p : Point) (hp : p∈IntegerCarrier rev100_planes) :
    p∈rationalHull (fractionRow100.map FractionPoint.rational) := by
  have hxlo := rev100_bound0_lo p hp
  have hxhi := rev100_bound0_hi p hp
  by_cases h0 : p.1≤rev100_s0_lr.real.1
  · exact rev100_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev100_s1_lr.real.1
  · exact rev100_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev100_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull100 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,0,15,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow100 := by
  rw [← fractionRow100_correct]
  exact rev100_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull100
