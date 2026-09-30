import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks2
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev21_planes : List IntegerPlane := integerOverlayPlanes ![2,0,15,8]
def rev21_plane7 : IntegerPlane := ⟨1855520000000,(-287616000000),1356143759600⟩
theorem rev21_plane7_mem : rev21_plane7 ∈ rev21_planes := by decide
def rev21_plane25 : IntegerPlane := ⟨(-2145688000000),(-699324000000),(-1695048727641)⟩
theorem rev21_plane25_mem : rev21_plane25 ∈ rev21_planes := by decide
def rev21_plane29 : IntegerPlane := ⟨(-2129316000000),1440116000000,(-1301343880216)⟩
theorem rev21_plane29_mem : rev21_plane29 ∈ rev21_planes := by decide
def rev21_plane55 : IntegerPlane := ⟨(-2139684000000),(-15204000000),(-1570721771568)⟩
theorem rev21_plane55_mem : rev21_plane55 ∈ rev21_planes := by decide
def rev21_vertex0 : FractionPoint := fractionRow21[0]!
theorem rev21_vertex0_mem : rev21_vertex0∈fractionRow21 := by decide
def rev21_vertex1 : FractionPoint := fractionRow21[1]!
theorem rev21_vertex1_mem : rev21_vertex1∈fractionRow21 := by decide
def rev21_vertex2 : FractionPoint := fractionRow21[2]!
theorem rev21_vertex2_mem : rev21_vertex2∈fractionRow21 := by decide
def rev21_vertex3 : FractionPoint := fractionRow21[3]!
theorem rev21_vertex3_mem : rev21_vertex3∈fractionRow21 := by decide
def rev21_s0_ll : FractionPoint := ⟨23768824866023187,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev21_s0_ll_mem : rev21_s0_ll.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane55 rev21_vertex2 rev21_vertex3 rev21_s0_ll
    rev21_vertex2_mem rev21_vertex3_mem (by decide)
def rev21_s0_lr : FractionPoint := ⟨89389325943747189,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev21_s0_lr_mem : rev21_s0_lr.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane55 rev21_vertex2 rev21_vertex3 rev21_s0_lr
    rev21_vertex2_mem rev21_vertex3_mem (by decide)
def rev21_s0_ul : FractionPoint := ⟨23768824866023187,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev21_s0_ul_mem : rev21_s0_ul.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane29 rev21_vertex2 rev21_vertex1 rev21_s0_ul
    rev21_vertex2_mem rev21_vertex1_mem (by decide)
def rev21_s0_ur : FractionPoint := ⟨89389325943747189,121975777772000000,7901422505764246533493,43914817295475388000000⟩
theorem rev21_s0_ur_mem : rev21_s0_ur.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane29 rev21_vertex2 rev21_vertex1 rev21_s0_ur
    rev21_vertex2_mem rev21_vertex1_mem (by decide)
theorem rev21_slab0 (p : Point) (hp : p∈IntegerCarrier rev21_planes)
    (hx0 : rev21_s0_ll.real.1≤p.1) (hx1 : p.1≤rev21_s0_lr.real.1) :
    p∈rationalHull (fractionRow21.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev21_plane55 rev21_plane29 rev21_s0_ll rev21_s0_lr rev21_s0_ul rev21_s0_ur
    (by decide) rev21_s0_ll_mem rev21_s0_lr_mem rev21_s0_ul_mem rev21_s0_ur_mem p
    (hp _ rev21_plane55_mem) (hp _ rev21_plane29_mem) hx0 hx1
def rev21_s1_ll : FractionPoint := ⟨89389325943747189,121975777772000000,4276496419360111,24395155554400000⟩
theorem rev21_s1_ll_mem : rev21_s1_ll.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane25 rev21_vertex3 rev21_vertex0 rev21_s1_ll
    rev21_vertex3_mem rev21_vertex0_mem (by decide)
def rev21_s1_lr : FractionPoint := ⟨7478682361394293,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev21_s1_lr_mem : rev21_s1_lr.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane25 rev21_vertex3 rev21_vertex0 rev21_s1_lr
    rev21_vertex3_mem rev21_vertex0_mem (by decide)
def rev21_s1_ul : FractionPoint := ⟨89389325943747189,121975777772000000,7901422505764246533493,43914817295475388000000⟩
theorem rev21_s1_ul_mem : rev21_s1_ul.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane29 rev21_vertex2 rev21_vertex1 rev21_s1_ul
    rev21_vertex2_mem rev21_vertex1_mem (by decide)
def rev21_s1_ur : FractionPoint := ⟨7478682361394293,9972624314000000,736666097579366305441,3590433959145106000000⟩
theorem rev21_s1_ur_mem : rev21_s1_ur.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane29 rev21_vertex2 rev21_vertex1 rev21_s1_ur
    rev21_vertex2_mem rev21_vertex1_mem (by decide)
theorem rev21_slab1 (p : Point) (hp : p∈IntegerCarrier rev21_planes)
    (hx0 : rev21_s1_ll.real.1≤p.1) (hx1 : p.1≤rev21_s1_lr.real.1) :
    p∈rationalHull (fractionRow21.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev21_plane25 rev21_plane29 rev21_s1_ll rev21_s1_lr rev21_s1_ul rev21_s1_ur
    (by decide) rev21_s1_ll_mem rev21_s1_lr_mem rev21_s1_ul_mem rev21_s1_ur_mem p
    (hp _ rev21_plane25_mem) (hp _ rev21_plane29_mem) hx0 hx1
def rev21_s2_ll : FractionPoint := ⟨7478682361394293,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev21_s2_ll_mem : rev21_s2_ll.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane7 rev21_vertex0 rev21_vertex1 rev21_s2_ll
    rev21_vertex0_mem rev21_vertex1_mem (by decide)
def rev21_s2_lr : FractionPoint := ⟨24667453203873571,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev21_s2_lr_mem : rev21_s2_lr.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane7 rev21_vertex0 rev21_vertex1 rev21_s2_lr
    rev21_vertex0_mem rev21_vertex1_mem (by decide)
def rev21_s2_ul : FractionPoint := ⟨7478682361394293,9972624314000000,736666097579366305441,3590433959145106000000⟩
theorem rev21_s2_ul_mem : rev21_s2_ul.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane29 rev21_vertex2 rev21_vertex1 rev21_s2_ul
    rev21_vertex2_mem rev21_vertex1_mem (by decide)
def rev21_s2_ur : FractionPoint := ⟨24667453203873571,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev21_s2_ur_mem : rev21_s2_ur.real ∈ rationalHull (fractionRow21.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow21 rev21_plane29 rev21_vertex2 rev21_vertex1 rev21_s2_ur
    rev21_vertex2_mem rev21_vertex1_mem (by decide)
theorem rev21_slab2 (p : Point) (hp : p∈IntegerCarrier rev21_planes)
    (hx0 : rev21_s2_ll.real.1≤p.1) (hx1 : p.1≤rev21_s2_lr.real.1) :
    p∈rationalHull (fractionRow21.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev21_plane7 rev21_plane29 rev21_s2_ll rev21_s2_lr rev21_s2_ul rev21_s2_ur
    (by decide) rev21_s2_ll_mem rev21_s2_lr_mem rev21_s2_ul_mem rev21_s2_ur_mem p
    (hp _ rev21_plane7_mem) (hp _ rev21_plane29_mem) hx0 hx1
theorem rev21_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev21_planes) : rev21_s0_ll.real.1≤p.1 := by
  have hc := rev21_plane29.combine_sound rev21_plane55 15204000000 1440116000000 (by decide) (by decide) p
    (hp _ rev21_plane29_mem) (hp _ rev21_plane55_mem)
  exact (rev21_plane29.combine rev21_plane55 15204000000 1440116000000).xBoundCheck_sound rev21_s0_ll.nx rev21_s0_ll.dx true (by decide) p hc
theorem rev21_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev21_planes) : p.1≤rev21_s2_lr.real.1 := by
  have hc := rev21_plane7.combine_sound rev21_plane29 1440116000000 287616000000 (by decide) (by decide) p
    (hp _ rev21_plane7_mem) (hp _ rev21_plane29_mem)
  exact (rev21_plane7.combine rev21_plane29 1440116000000 287616000000).xBoundCheck_sound rev21_s2_lr.nx rev21_s2_lr.dx false (by decide) p hc
theorem rev21_hull (p : Point) (hp : p∈IntegerCarrier rev21_planes) :
    p∈rationalHull (fractionRow21.map FractionPoint.rational) := by
  have hxlo := rev21_bound0_lo p hp
  have hxhi := rev21_bound0_hi p hp
  by_cases h0 : p.1≤rev21_s0_lr.real.1
  · exact rev21_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev21_s1_lr.real.1
  · exact rev21_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev21_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull21 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,0,15,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow21 := by
  rw [← fractionRow21_correct]
  exact rev21_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull21
