import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks26
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev215_planes : List IntegerPlane := integerOverlayPlanes ![15,8,13,15]
def rev215_plane15 : IntegerPlane := ⟨15204000000,(-2139684000000),(-1555517771568)⟩
theorem rev215_plane15_mem : rev215_plane15 ∈ rev215_planes := by decide
def rev215_plane56 : IntegerPlane := ⟨287616000000,1855520000000,1643759759600⟩
theorem rev215_plane56_mem : rev215_plane56 ∈ rev215_planes := by decide
def rev215_plane74 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-2741459880216)⟩
theorem rev215_plane74_mem : rev215_plane74 ∈ rev215_planes := by decide
def rev215_plane78 : IntegerPlane := ⟨699324000000,(-2145688000000),(-995724727641)⟩
theorem rev215_plane78_mem : rev215_plane78 ∈ rev215_planes := by decide
def rev215_vertex0 : FractionPoint := fractionRow215[0]!
theorem rev215_vertex0_mem : rev215_vertex0∈fractionRow215 := by decide
def rev215_vertex1 : FractionPoint := fractionRow215[1]!
theorem rev215_vertex1_mem : rev215_vertex1∈fractionRow215 := by decide
def rev215_vertex2 : FractionPoint := fractionRow215[2]!
theorem rev215_vertex2_mem : rev215_vertex2∈fractionRow215 := by decide
def rev215_vertex3 : FractionPoint := fractionRow215[3]!
theorem rev215_vertex3_mem : rev215_vertex3∈fractionRow215 := by decide
def rev215_s0_ll : FractionPoint := ⟨4958592752081121,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev215_s0_ll_mem : rev215_s0_ll.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane74 rev215_vertex3 rev215_vertex0 rev215_s0_ll
    rev215_vertex3_mem rev215_vertex0_mem (by decide)
def rev215_s0_lr : FractionPoint := ⟨26600718365166711,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev215_s0_lr_mem : rev215_s0_lr.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane74 rev215_vertex3 rev215_vertex0 rev215_s0_lr
    rev215_vertex3_mem rev215_vertex0_mem (by decide)
def rev215_s0_ul : FractionPoint := ⟨4958592752081121,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev215_s0_ul_mem : rev215_s0_ul.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane56 rev215_vertex3 rev215_vertex2 rev215_s0_ul
    rev215_vertex3_mem rev215_vertex2_mem (by decide)
def rev215_s0_ur : FractionPoint := ⟨26600718365166711,32435075873000000,2854042519143403211239,3761495748991810000000⟩
theorem rev215_s0_ur_mem : rev215_s0_ur.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane56 rev215_vertex3 rev215_vertex2 rev215_s0_ur
    rev215_vertex3_mem rev215_vertex2_mem (by decide)
theorem rev215_slab0 (p : Point) (hp : p∈IntegerCarrier rev215_planes)
    (hx0 : rev215_s0_ll.real.1≤p.1) (hx1 : p.1≤rev215_s0_lr.real.1) :
    p∈rationalHull (fractionRow215.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev215_plane74 rev215_plane56 rev215_s0_ll rev215_s0_lr rev215_s0_ul rev215_s0_ur
    (by decide) rev215_s0_ll_mem rev215_s0_lr_mem rev215_s0_ul_mem rev215_s0_ur_mem p
    (hp _ rev215_plane74_mem) (hp _ rev215_plane56_mem) hx0 hx1
def rev215_s1_ll : FractionPoint := ⟨26600718365166711,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev215_s1_ll_mem : rev215_s1_ll.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane15 rev215_vertex0 rev215_vertex1 rev215_s1_ll
    rev215_vertex0_mem rev215_vertex1_mem (by decide)
def rev215_s1_lr : FractionPoint := ⟨20118659135039889,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev215_s1_lr_mem : rev215_s1_lr.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane15 rev215_vertex0 rev215_vertex1 rev215_s1_lr
    rev215_vertex0_mem rev215_vertex1_mem (by decide)
def rev215_s1_ul : FractionPoint := ⟨26600718365166711,32435075873000000,2854042519143403211239,3761495748991810000000⟩
theorem rev215_s1_ul_mem : rev215_s1_ul.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane56 rev215_vertex3 rev215_vertex2 rev215_s1_ul
    rev215_vertex3_mem rev215_vertex2_mem (by decide)
def rev215_s1_ur : FractionPoint := ⟨20118659135039889,24395155554400000,536145730683148687619,707276547410942000000⟩
theorem rev215_s1_ur_mem : rev215_s1_ur.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane56 rev215_vertex3 rev215_vertex2 rev215_s1_ur
    rev215_vertex3_mem rev215_vertex2_mem (by decide)
theorem rev215_slab1 (p : Point) (hp : p∈IntegerCarrier rev215_planes)
    (hx0 : rev215_s1_ll.real.1≤p.1) (hx1 : p.1≤rev215_s1_lr.real.1) :
    p∈rationalHull (fractionRow215.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev215_plane15 rev215_plane56 rev215_s1_ll rev215_s1_lr rev215_s1_ul rev215_s1_ur
    (by decide) rev215_s1_ll_mem rev215_s1_lr_mem rev215_s1_ul_mem rev215_s1_ur_mem p
    (hp _ rev215_plane15_mem) (hp _ rev215_plane56_mem) hx0 hx1
def rev215_s2_ll : FractionPoint := ⟨20118659135039889,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev215_s2_ll_mem : rev215_s2_ll.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane78 rev215_vertex1 rev215_vertex2 rev215_s2_ll
    rev215_vertex1_mem rev215_vertex2_mem (by decide)
def rev215_s2_lr : FractionPoint := ⟨10496302777651103,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev215_s2_lr_mem : rev215_s2_lr.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane78 rev215_vertex1 rev215_vertex2 rev215_s2_lr
    rev215_vertex1_mem rev215_vertex2_mem (by decide)
def rev215_s2_ul : FractionPoint := ⟨20118659135039889,24395155554400000,536145730683148687619,707276547410942000000⟩
theorem rev215_s2_ul_mem : rev215_s2_ul.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane56 rev215_vertex3 rev215_vertex2 rev215_s2_ul
    rev215_vertex3_mem rev215_vertex2_mem (by decide)
def rev215_s2_ur : FractionPoint := ⟨10496302777651103,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev215_s2_ur_mem : rev215_s2_ur.real ∈ rationalHull (fractionRow215.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow215 rev215_plane56 rev215_vertex3 rev215_vertex2 rev215_s2_ur
    rev215_vertex3_mem rev215_vertex2_mem (by decide)
theorem rev215_slab2 (p : Point) (hp : p∈IntegerCarrier rev215_planes)
    (hx0 : rev215_s2_ll.real.1≤p.1) (hx1 : p.1≤rev215_s2_lr.real.1) :
    p∈rationalHull (fractionRow215.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev215_plane78 rev215_plane56 rev215_s2_ll rev215_s2_lr rev215_s2_ul rev215_s2_ur
    (by decide) rev215_s2_ll_mem rev215_s2_lr_mem rev215_s2_ul_mem rev215_s2_ur_mem p
    (hp _ rev215_plane78_mem) (hp _ rev215_plane56_mem) hx0 hx1
theorem rev215_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev215_planes) : rev215_s0_ll.real.1≤p.1 := by
  have hc := rev215_plane56.combine_sound rev215_plane74 2129316000000 1855520000000 (by decide) (by decide) p
    (hp _ rev215_plane56_mem) (hp _ rev215_plane74_mem)
  exact (rev215_plane56.combine rev215_plane74 2129316000000 1855520000000).xBoundCheck_sound rev215_s0_ll.nx rev215_s0_ll.dx true (by decide) p hc
theorem rev215_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev215_planes) : p.1≤rev215_s2_lr.real.1 := by
  have hc := rev215_plane56.combine_sound rev215_plane78 2145688000000 1855520000000 (by decide) (by decide) p
    (hp _ rev215_plane56_mem) (hp _ rev215_plane78_mem)
  exact (rev215_plane56.combine rev215_plane78 2145688000000 1855520000000).xBoundCheck_sound rev215_s2_lr.nx rev215_s2_lr.dx false (by decide) p hc
theorem rev215_hull (p : Point) (hp : p∈IntegerCarrier rev215_planes) :
    p∈rationalHull (fractionRow215.map FractionPoint.rational) := by
  have hxlo := rev215_bound0_lo p hp
  have hxhi := rev215_bound0_hi p hp
  by_cases h0 : p.1≤rev215_s0_lr.real.1
  · exact rev215_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev215_s1_lr.real.1
  · exact rev215_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev215_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull215 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,8,13,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow215 := by
  rw [← fractionRow215_correct]
  exact rev215_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull215
