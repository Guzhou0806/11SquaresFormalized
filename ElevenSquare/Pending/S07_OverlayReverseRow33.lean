import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks4
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev33_planes : List IntegerPlane := integerOverlayPlanes ![2,5,15,8]
def rev33_plane7 : IntegerPlane := ⟨1855520000000,(-287616000000),1356143759600⟩
theorem rev33_plane7_mem : rev33_plane7 ∈ rev33_planes := by decide
def rev33_plane24 : IntegerPlane := ⟨2129316000000,(-1440116000000),1301343880216⟩
theorem rev33_plane24_mem : rev33_plane24 ∈ rev33_planes := by decide
def rev33_plane54 : IntegerPlane := ⟨(-1440116000000),2129316000000,(-612143880216)⟩
theorem rev33_plane54_mem : rev33_plane54 ∈ rev33_planes := by decide
def rev33_plane55 : IntegerPlane := ⟨(-2139684000000),(-15204000000),(-1570721771568)⟩
theorem rev33_plane55_mem : rev33_plane55 ∈ rev33_planes := by decide
def rev33_vertex0 : FractionPoint := fractionRow33[0]!
theorem rev33_vertex0_mem : rev33_vertex0∈fractionRow33 := by decide
def rev33_vertex1 : FractionPoint := fractionRow33[1]!
theorem rev33_vertex1_mem : rev33_vertex1∈fractionRow33 := by decide
def rev33_vertex2 : FractionPoint := fractionRow33[2]!
theorem rev33_vertex2_mem : rev33_vertex2∈fractionRow33 := by decide
def rev33_vertex3 : FractionPoint := fractionRow33[3]!
theorem rev33_vertex3_mem : rev33_vertex3∈fractionRow33 := by decide
def rev33_s0_ll : FractionPoint := ⟨216994696901067,296192993000000,431262268381943,2073350951000000⟩
theorem rev33_s0_ll_mem : rev33_s0_ll.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane55 rev33_vertex2 rev33_vertex3 rev33_s0_ll
    rev33_vertex2_mem rev33_vertex3_mem (by decide)
def rev33_s0_lr : FractionPoint := ⟨23768824866023187,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev33_s0_lr_mem : rev33_s0_lr.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane55 rev33_vertex2 rev33_vertex3 rev33_s0_lr
    rev33_vertex2_mem rev33_vertex3_mem (by decide)
def rev33_s0_ul : FractionPoint := ⟨216994696901067,296192993000000,431262268381943,2073350951000000⟩
theorem rev33_s0_ul_mem : rev33_s0_ul.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane54 rev33_vertex2 rev33_vertex1 rev33_s0_ul
    rev33_vertex2_mem rev33_vertex1_mem (by decide)
def rev33_s0_ur : FractionPoint := ⟨23768824866023187,32435075873000000,1197910982563272028427,5755377168132739000000⟩
theorem rev33_s0_ur_mem : rev33_s0_ur.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane54 rev33_vertex2 rev33_vertex1 rev33_s0_ur
    rev33_vertex2_mem rev33_vertex1_mem (by decide)
theorem rev33_slab0 (p : Point) (hp : p∈IntegerCarrier rev33_planes)
    (hx0 : rev33_s0_ll.real.1≤p.1) (hx1 : p.1≤rev33_s0_lr.real.1) :
    p∈rationalHull (fractionRow33.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev33_plane55 rev33_plane54 rev33_s0_ll rev33_s0_lr rev33_s0_ul rev33_s0_ur
    (by decide) rev33_s0_ll_mem rev33_s0_lr_mem rev33_s0_ul_mem rev33_s0_ur_mem p
    (hp _ rev33_plane55_mem) (hp _ rev33_plane54_mem) hx0 hx1
def rev33_s1_ll : FractionPoint := ⟨23768824866023187,32435075873000000,5834357507833289,32435075873000000⟩
theorem rev33_s1_ll_mem : rev33_s1_ll.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane24 rev33_vertex3 rev33_vertex0 rev33_s1_ll
    rev33_vertex3_mem rev33_vertex0_mem (by decide)
def rev33_s1_lr : FractionPoint := ⟨24667453203873571,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev33_s1_lr_mem : rev33_s1_lr.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane24 rev33_vertex3 rev33_vertex0 rev33_s1_lr
    rev33_vertex3_mem rev33_vertex0_mem (by decide)
def rev33_s1_ul : FractionPoint := ⟨23768824866023187,32435075873000000,1197910982563272028427,5755377168132739000000⟩
theorem rev33_s1_ul_mem : rev33_s1_ul.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane54 rev33_vertex2 rev33_vertex1 rev33_s1_ul
    rev33_vertex2_mem rev33_vertex1_mem (by decide)
def rev33_s1_ur : FractionPoint := ⟨24667453203873571,32183417026000000,791155613062213630831,3426433240406710800000⟩
theorem rev33_s1_ur_mem : rev33_s1_ur.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane54 rev33_vertex2 rev33_vertex1 rev33_s1_ur
    rev33_vertex2_mem rev33_vertex1_mem (by decide)
theorem rev33_slab1 (p : Point) (hp : p∈IntegerCarrier rev33_planes)
    (hx0 : rev33_s1_ll.real.1≤p.1) (hx1 : p.1≤rev33_s1_lr.real.1) :
    p∈rationalHull (fractionRow33.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev33_plane24 rev33_plane54 rev33_s1_ll rev33_s1_lr rev33_s1_ul rev33_s1_ur
    (by decide) rev33_s1_ll_mem rev33_s1_lr_mem rev33_s1_ul_mem rev33_s1_ur_mem p
    (hp _ rev33_plane24_mem) (hp _ rev33_plane54_mem) hx0 hx1
def rev33_s2_ll : FractionPoint := ⟨24667453203873571,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev33_s2_ll_mem : rev33_s2_ll.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane7 rev33_vertex0 rev33_vertex1 rev33_s2_ll
    rev33_vertex0_mem rev33_vertex1_mem (by decide)
def rev33_s2_lr : FractionPoint := ⟨2017556719765051,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev33_s2_lr_mem : rev33_s2_lr.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane7 rev33_vertex0 rev33_vertex1 rev33_s2_lr
    rev33_vertex0_mem rev33_vertex1_mem (by decide)
def rev33_s2_ul : FractionPoint := ⟨24667453203873571,32183417026000000,791155613062213630831,3426433240406710800000⟩
theorem rev33_s2_ul_mem : rev33_s2_ul.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane54 rev33_vertex2 rev33_vertex1 rev33_s2_ul
    rev33_vertex2_mem rev33_vertex1_mem (by decide)
def rev33_s2_ur : FractionPoint := ⟨2017556719765051,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev33_s2_ur_mem : rev33_s2_ur.real ∈ rationalHull (fractionRow33.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow33 rev33_plane54 rev33_vertex2 rev33_vertex1 rev33_s2_ur
    rev33_vertex2_mem rev33_vertex1_mem (by decide)
theorem rev33_slab2 (p : Point) (hp : p∈IntegerCarrier rev33_planes)
    (hx0 : rev33_s2_ll.real.1≤p.1) (hx1 : p.1≤rev33_s2_lr.real.1) :
    p∈rationalHull (fractionRow33.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev33_plane7 rev33_plane54 rev33_s2_ll rev33_s2_lr rev33_s2_ul rev33_s2_ur
    (by decide) rev33_s2_ll_mem rev33_s2_lr_mem rev33_s2_ul_mem rev33_s2_ur_mem p
    (hp _ rev33_plane7_mem) (hp _ rev33_plane54_mem) hx0 hx1
theorem rev33_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev33_planes) : rev33_s0_ll.real.1≤p.1 := by
  have hc := rev33_plane54.combine_sound rev33_plane55 15204000000 2129316000000 (by decide) (by decide) p
    (hp _ rev33_plane54_mem) (hp _ rev33_plane55_mem)
  exact (rev33_plane54.combine rev33_plane55 15204000000 2129316000000).xBoundCheck_sound rev33_s0_ll.nx rev33_s0_ll.dx true (by decide) p hc
theorem rev33_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev33_planes) : p.1≤rev33_s2_lr.real.1 := by
  have hc := rev33_plane7.combine_sound rev33_plane54 2129316000000 287616000000 (by decide) (by decide) p
    (hp _ rev33_plane7_mem) (hp _ rev33_plane54_mem)
  exact (rev33_plane7.combine rev33_plane54 2129316000000 287616000000).xBoundCheck_sound rev33_s2_lr.nx rev33_s2_lr.dx false (by decide) p hc
theorem rev33_hull (p : Point) (hp : p∈IntegerCarrier rev33_planes) :
    p∈rationalHull (fractionRow33.map FractionPoint.rational) := by
  have hxlo := rev33_bound0_lo p hp
  have hxhi := rev33_bound0_hi p hp
  by_cases h0 : p.1≤rev33_s0_lr.real.1
  · exact rev33_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev33_s1_lr.real.1
  · exact rev33_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev33_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull33 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,5,15,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow33 := by
  rw [← fractionRow33_correct]
  exact rev33_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull33
