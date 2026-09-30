import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks14
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev119_planes : List IntegerPlane := integerOverlayPlanes ![8,15,0,2]
def rev119_plane35 : IntegerPlane := ⟨(-15204000000),(-2139684000000),(-1570721771568)⟩
theorem rev119_plane35_mem : rev119_plane35 ∈ rev119_planes := by decide
def rev119_plane45 : IntegerPlane := ⟨(-699324000000),(-2145688000000),(-1695048727641)⟩
theorem rev119_plane45_mem : rev119_plane45 ∈ rev119_planes := by decide
def rev119_plane49 : IntegerPlane := ⟨1440116000000,(-2129316000000),(-1301343880216)⟩
theorem rev119_plane49_mem : rev119_plane49 ∈ rev119_planes := by decide
def rev119_plane67 : IntegerPlane := ⟨(-287616000000),1855520000000,1356143759600⟩
theorem rev119_plane67_mem : rev119_plane67 ∈ rev119_planes := by decide
def rev119_vertex0 : FractionPoint := fractionRow119[0]!
theorem rev119_vertex0_mem : rev119_vertex0∈fractionRow119 := by decide
def rev119_vertex1 : FractionPoint := fractionRow119[1]!
theorem rev119_vertex1_mem : rev119_vertex1∈fractionRow119 := by decide
def rev119_vertex2 : FractionPoint := fractionRow119[2]!
theorem rev119_vertex2_mem : rev119_vertex2∈fractionRow119 := by decide
def rev119_vertex3 : FractionPoint := fractionRow119[3]!
theorem rev119_vertex3_mem : rev119_vertex3∈fractionRow119 := by decide
def rev119_s0_ll : FractionPoint := ⟨1470846399148897,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev119_s0_ll_mem : rev119_s0_ll.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane45 rev119_vertex0 rev119_vertex1 rev119_s0_ll
    rev119_vertex0_mem rev119_vertex1_mem (by decide)
def rev119_s0_lr : FractionPoint := ⟨4276496419360111,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev119_s0_lr_mem : rev119_s0_lr.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane45 rev119_vertex0 rev119_vertex1 rev119_s0_lr
    rev119_vertex0_mem rev119_vertex1_mem (by decide)
def rev119_s0_ul : FractionPoint := ⟨1470846399148897,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev119_s0_ul_mem : rev119_s0_ul.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane67 rev119_vertex0 rev119_vertex3 rev119_s0_ul
    rev119_vertex0_mem rev119_vertex3_mem (by decide)
def rev119_s0_ur : FractionPoint := ⟨4276496419360111,24395155554400000,536145730683148687619,707276547410942000000⟩
theorem rev119_s0_ur_mem : rev119_s0_ur.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane67 rev119_vertex0 rev119_vertex3 rev119_s0_ur
    rev119_vertex0_mem rev119_vertex3_mem (by decide)
theorem rev119_slab0 (p : Point) (hp : p∈IntegerCarrier rev119_planes)
    (hx0 : rev119_s0_ll.real.1≤p.1) (hx1 : p.1≤rev119_s0_lr.real.1) :
    p∈rationalHull (fractionRow119.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev119_plane45 rev119_plane67 rev119_s0_ll rev119_s0_lr rev119_s0_ul rev119_s0_ur
    (by decide) rev119_s0_ll_mem rev119_s0_lr_mem rev119_s0_ul_mem rev119_s0_ur_mem p
    (hp _ rev119_plane45_mem) (hp _ rev119_plane67_mem) hx0 hx1
def rev119_s1_ll : FractionPoint := ⟨4276496419360111,24395155554400000,89389325943747189,121975777772000000⟩
theorem rev119_s1_ll_mem : rev119_s1_ll.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane35 rev119_vertex1 rev119_vertex2 rev119_s1_ll
    rev119_vertex1_mem rev119_vertex2_mem (by decide)
def rev119_s1_lr : FractionPoint := ⟨5834357507833289,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev119_s1_lr_mem : rev119_s1_lr.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane35 rev119_vertex1 rev119_vertex2 rev119_s1_lr
    rev119_vertex1_mem rev119_vertex2_mem (by decide)
def rev119_s1_ul : FractionPoint := ⟨4276496419360111,24395155554400000,536145730683148687619,707276547410942000000⟩
theorem rev119_s1_ul_mem : rev119_s1_ul.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane67 rev119_vertex0 rev119_vertex3 rev119_s1_ul
    rev119_vertex0_mem rev119_vertex3_mem (by decide)
def rev119_s1_ur : FractionPoint := ⟨5834357507833289,32435075873000000,2854042519143403211239,3761495748991810000000⟩
theorem rev119_s1_ur_mem : rev119_s1_ur.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane67 rev119_vertex0 rev119_vertex3 rev119_s1_ur
    rev119_vertex0_mem rev119_vertex3_mem (by decide)
theorem rev119_slab1 (p : Point) (hp : p∈IntegerCarrier rev119_planes)
    (hx0 : rev119_s1_ll.real.1≤p.1) (hx1 : p.1≤rev119_s1_lr.real.1) :
    p∈rationalHull (fractionRow119.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev119_plane35 rev119_plane67 rev119_s1_ll rev119_s1_lr rev119_s1_ul rev119_s1_ur
    (by decide) rev119_s1_ll_mem rev119_s1_lr_mem rev119_s1_ul_mem rev119_s1_ur_mem p
    (hp _ rev119_plane35_mem) (hp _ rev119_plane67_mem) hx0 hx1
def rev119_s2_ll : FractionPoint := ⟨5834357507833289,32435075873000000,23768824866023187,32435075873000000⟩
theorem rev119_s2_ll_mem : rev119_s2_ll.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane49 rev119_vertex2 rev119_vertex3 rev119_s2_ll
    rev119_vertex2_mem rev119_vertex3_mem (by decide)
def rev119_s2_lr : FractionPoint := ⟨1478090653118879,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev119_s2_lr_mem : rev119_s2_lr.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane49 rev119_vertex2 rev119_vertex3 rev119_s2_lr
    rev119_vertex2_mem rev119_vertex3_mem (by decide)
def rev119_s2_ul : FractionPoint := ⟨5834357507833289,32435075873000000,2854042519143403211239,3761495748991810000000⟩
theorem rev119_s2_ul_mem : rev119_s2_ul.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane67 rev119_vertex0 rev119_vertex3 rev119_s2_ul
    rev119_vertex0_mem rev119_vertex3_mem (by decide)
def rev119_s2_ur : FractionPoint := ⟨1478090653118879,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev119_s2_ur_mem : rev119_s2_ur.real ∈ rationalHull (fractionRow119.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow119 rev119_plane67 rev119_vertex0 rev119_vertex3 rev119_s2_ur
    rev119_vertex0_mem rev119_vertex3_mem (by decide)
theorem rev119_slab2 (p : Point) (hp : p∈IntegerCarrier rev119_planes)
    (hx0 : rev119_s2_ll.real.1≤p.1) (hx1 : p.1≤rev119_s2_lr.real.1) :
    p∈rationalHull (fractionRow119.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev119_plane49 rev119_plane67 rev119_s2_ll rev119_s2_lr rev119_s2_ul rev119_s2_ur
    (by decide) rev119_s2_ll_mem rev119_s2_lr_mem rev119_s2_ul_mem rev119_s2_ur_mem p
    (hp _ rev119_plane49_mem) (hp _ rev119_plane67_mem) hx0 hx1
theorem rev119_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev119_planes) : rev119_s0_ll.real.1≤p.1 := by
  have hc := rev119_plane45.combine_sound rev119_plane67 1855520000000 2145688000000 (by decide) (by decide) p
    (hp _ rev119_plane45_mem) (hp _ rev119_plane67_mem)
  exact (rev119_plane45.combine rev119_plane67 1855520000000 2145688000000).xBoundCheck_sound rev119_s0_ll.nx rev119_s0_ll.dx true (by decide) p hc
theorem rev119_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev119_planes) : p.1≤rev119_s2_lr.real.1 := by
  have hc := rev119_plane49.combine_sound rev119_plane67 1855520000000 2129316000000 (by decide) (by decide) p
    (hp _ rev119_plane49_mem) (hp _ rev119_plane67_mem)
  exact (rev119_plane49.combine rev119_plane67 1855520000000 2129316000000).xBoundCheck_sound rev119_s2_lr.nx rev119_s2_lr.dx false (by decide) p hc
theorem rev119_hull (p : Point) (hp : p∈IntegerCarrier rev119_planes) :
    p∈rationalHull (fractionRow119.map FractionPoint.rational) := by
  have hxlo := rev119_bound0_lo p hp
  have hxhi := rev119_bound0_hi p hp
  by_cases h0 : p.1≤rev119_s0_lr.real.1
  · exact rev119_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev119_s1_lr.real.1
  · exact rev119_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev119_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull119 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,15,0,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow119 := by
  rw [← fractionRow119_correct]
  exact rev119_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull119
