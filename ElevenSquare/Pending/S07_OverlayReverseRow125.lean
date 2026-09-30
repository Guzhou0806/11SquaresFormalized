import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks15
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev125_planes : List IntegerPlane := integerOverlayPlanes ![8,15,5,3]
def rev125_plane34 : IntegerPlane := ⟨2129316000000,(-1440116000000),(-612143880216)⟩
theorem rev125_plane34_mem : rev125_plane34 ∈ rev125_planes := by decide
def rev125_plane44 : IntegerPlane := ⟨(-1440116000000),2129316000000,1301343880216⟩
theorem rev125_plane44_mem : rev125_plane44 ∈ rev125_planes := by decide
def rev125_plane66 : IntegerPlane := ⟨287616000000,(-1855520000000),(-1356143759600)⟩
theorem rev125_plane66_mem : rev125_plane66 ∈ rev125_planes := by decide
def rev125_plane71 : IntegerPlane := ⟨1861776000000,202532000000,585903739447⟩
theorem rev125_plane71_mem : rev125_plane71 ∈ rev125_planes := by decide
def rev125_vertex0 : FractionPoint := fractionRow125[0]!
theorem rev125_vertex0_mem : rev125_vertex0∈fractionRow125 := by decide
def rev125_vertex1 : FractionPoint := fractionRow125[1]!
theorem rev125_vertex1_mem : rev125_vertex1∈fractionRow125 := by decide
def rev125_vertex2 : FractionPoint := fractionRow125[2]!
theorem rev125_vertex2_mem : rev125_vertex2∈fractionRow125 := by decide
def rev125_vertex3 : FractionPoint := fractionRow125[3]!
theorem rev125_vertex3_mem : rev125_vertex3∈fractionRow125 := by decide
def rev125_s0_ll : FractionPoint := ⟨1478090653118879,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev125_s0_ll_mem : rev125_s0_ll.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane66 rev125_vertex3 rev125_vertex0 rev125_s0_ll
    rev125_vertex3_mem rev125_vertex0_mem (by decide)
def rev125_s0_lr : FractionPoint := ⟨2553622230880379,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev125_s0_lr_mem : rev125_s0_lr.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane66 rev125_vertex3 rev125_vertex0 rev125_s0_lr
    rev125_vertex3_mem rev125_vertex0_mem (by decide)
def rev125_s0_ul : FractionPoint := ⟨1478090653118879,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev125_s0_ul_mem : rev125_s0_ul.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane44 rev125_vertex3 rev125_vertex2 rev125_s0_ul
    rev125_vertex3_mem rev125_vertex2_mem (by decide)
def rev125_s0_ur : FractionPoint := ⟨2553622230880379,11052462565200000,22575708441482475967559,29417731724351754000000⟩
theorem rev125_s0_ur_mem : rev125_s0_ur.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane44 rev125_vertex3 rev125_vertex2 rev125_s0_ur
    rev125_vertex3_mem rev125_vertex2_mem (by decide)
theorem rev125_slab0 (p : Point) (hp : p∈IntegerCarrier rev125_planes)
    (hx0 : rev125_s0_ll.real.1≤p.1) (hx1 : p.1≤rev125_s0_lr.real.1) :
    p∈rationalHull (fractionRow125.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev125_plane66 rev125_plane44 rev125_s0_ll rev125_s0_lr rev125_s0_ul rev125_s0_ur
    (by decide) rev125_s0_ll_mem rev125_s0_lr_mem rev125_s0_ul_mem rev125_s0_ur_mem p
    (hp _ rev125_plane66_mem) (hp _ rev125_plane44_mem) hx0 hx1
def rev125_s1_ll : FractionPoint := ⟨2553622230880379,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev125_s1_ll_mem : rev125_s1_ll.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane34 rev125_vertex0 rev125_vertex1 rev125_s1_ll
    rev125_vertex0_mem rev125_vertex1_mem (by decide)
def rev125_s1_lr : FractionPoint := ⟨49200521405821067,212798949946400000,293783790454796190400743,383068965751262228000000⟩
theorem rev125_s1_lr_mem : rev125_s1_lr.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane34 rev125_vertex0 rev125_vertex1 rev125_s1_lr
    rev125_vertex0_mem rev125_vertex1_mem (by decide)
def rev125_s1_ul : FractionPoint := ⟨2553622230880379,11052462565200000,22575708441482475967559,29417731724351754000000⟩
theorem rev125_s1_ul_mem : rev125_s1_ul.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane44 rev125_vertex3 rev125_vertex2 rev125_s1_ul
    rev125_vertex3_mem rev125_vertex2_mem (by decide)
def rev125_s1_ur : FractionPoint := ⟨49200521405821067,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev125_s1_ur_mem : rev125_s1_ur.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane44 rev125_vertex3 rev125_vertex2 rev125_s1_ur
    rev125_vertex3_mem rev125_vertex2_mem (by decide)
theorem rev125_slab1 (p : Point) (hp : p∈IntegerCarrier rev125_planes)
    (hx0 : rev125_s1_ll.real.1≤p.1) (hx1 : p.1≤rev125_s1_lr.real.1) :
    p∈rationalHull (fractionRow125.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev125_plane34 rev125_plane44 rev125_s1_ll rev125_s1_lr rev125_s1_ul rev125_s1_ur
    (by decide) rev125_s1_ll_mem rev125_s1_lr_mem rev125_s1_ul_mem rev125_s1_ur_mem p
    (hp _ rev125_plane34_mem) (hp _ rev125_plane44_mem) hx0 hx1
def rev125_s2_ll : FractionPoint := ⟨49200521405821067,212798949946400000,293783790454796190400743,383068965751262228000000⟩
theorem rev125_s2_ll_mem : rev125_s2_ll.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane34 rev125_vertex0 rev125_vertex1 rev125_s2_ll
    rev125_vertex0_mem rev125_vertex1_mem (by decide)
def rev125_s2_lr : FractionPoint := ⟨35989531264477447,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev125_s2_lr_mem : rev125_s2_lr.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane34 rev125_vertex0 rev125_vertex1 rev125_s2_lr
    rev125_vertex0_mem rev125_vertex1_mem (by decide)
def rev125_s2_ul : FractionPoint := ⟨49200521405821067,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev125_s2_ul_mem : rev125_s2_ul.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane71 rev125_vertex2 rev125_vertex1 rev125_s2_ul
    rev125_vertex2_mem rev125_vertex1_mem (by decide)
def rev125_s2_ur : FractionPoint := ⟨35989531264477447,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev125_s2_ur_mem : rev125_s2_ur.real ∈ rationalHull (fractionRow125.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow125 rev125_plane71 rev125_vertex2 rev125_vertex1 rev125_s2_ur
    rev125_vertex2_mem rev125_vertex1_mem (by decide)
theorem rev125_slab2 (p : Point) (hp : p∈IntegerCarrier rev125_planes)
    (hx0 : rev125_s2_ll.real.1≤p.1) (hx1 : p.1≤rev125_s2_lr.real.1) :
    p∈rationalHull (fractionRow125.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev125_plane34 rev125_plane71 rev125_s2_ll rev125_s2_lr rev125_s2_ul rev125_s2_ur
    (by decide) rev125_s2_ll_mem rev125_s2_lr_mem rev125_s2_ul_mem rev125_s2_ur_mem p
    (hp _ rev125_plane34_mem) (hp _ rev125_plane71_mem) hx0 hx1
theorem rev125_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev125_planes) : rev125_s0_ll.real.1≤p.1 := by
  have hc := rev125_plane44.combine_sound rev125_plane66 1855520000000 2129316000000 (by decide) (by decide) p
    (hp _ rev125_plane44_mem) (hp _ rev125_plane66_mem)
  exact (rev125_plane44.combine rev125_plane66 1855520000000 2129316000000).xBoundCheck_sound rev125_s0_ll.nx rev125_s0_ll.dx true (by decide) p hc
theorem rev125_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev125_planes) : p.1≤rev125_s2_lr.real.1 := by
  have hc := rev125_plane34.combine_sound rev125_plane71 202532000000 1440116000000 (by decide) (by decide) p
    (hp _ rev125_plane34_mem) (hp _ rev125_plane71_mem)
  exact (rev125_plane34.combine rev125_plane71 202532000000 1440116000000).xBoundCheck_sound rev125_s2_lr.nx rev125_s2_lr.dx false (by decide) p hc
theorem rev125_hull (p : Point) (hp : p∈IntegerCarrier rev125_planes) :
    p∈rationalHull (fractionRow125.map FractionPoint.rational) := by
  have hxlo := rev125_bound0_lo p hp
  have hxhi := rev125_bound0_hi p hp
  by_cases h0 : p.1≤rev125_s0_lr.real.1
  · exact rev125_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev125_s1_lr.real.1
  · exact rev125_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev125_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull125 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,15,5,3] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow125 := by
  rw [← fractionRow125_correct]
  exact rev125_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull125
