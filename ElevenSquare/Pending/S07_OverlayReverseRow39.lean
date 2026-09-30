import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks4
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev39_planes : List IntegerPlane := integerOverlayPlanes ![3,5,15,8]
def rev39_plane6 : IntegerPlane := ⟨(-1855520000000),287616000000,(-1356143759600)⟩
theorem rev39_plane6_mem : rev39_plane6 ∈ rev39_planes := by decide
def rev39_plane11 : IntegerPlane := ⟨202532000000,1861776000000,585903739447⟩
theorem rev39_plane11_mem : rev39_plane11 ∈ rev39_planes := by decide
def rev39_plane24 : IntegerPlane := ⟨2129316000000,(-1440116000000),1301343880216⟩
theorem rev39_plane24_mem : rev39_plane24 ∈ rev39_planes := by decide
def rev39_plane54 : IntegerPlane := ⟨(-1440116000000),2129316000000,(-612143880216)⟩
theorem rev39_plane54_mem : rev39_plane54 ∈ rev39_planes := by decide
def rev39_vertex0 : FractionPoint := fractionRow39[0]!
theorem rev39_vertex0_mem : rev39_vertex0∈fractionRow39 := by decide
def rev39_vertex1 : FractionPoint := fractionRow39[1]!
theorem rev39_vertex1_mem : rev39_vertex1∈fractionRow39 := by decide
def rev39_vertex2 : FractionPoint := fractionRow39[2]!
theorem rev39_vertex2_mem : rev39_vertex2∈fractionRow39 := by decide
def rev39_vertex3 : FractionPoint := fractionRow39[3]!
theorem rev39_vertex3_mem : rev39_vertex3∈fractionRow39 := by decide
def rev39_s0_ll : FractionPoint := ⟨24667453203873571,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev39_s0_ll_mem : rev39_s0_ll.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane24 rev39_vertex3 rev39_vertex0 rev39_s0_ll
    rev39_vertex3_mem rev39_vertex0_mem (by decide)
def rev39_s0_lr : FractionPoint := ⟨2017556719765051,2631538706000000,43573950684930384731,189486049756494800000⟩
theorem rev39_s0_lr_mem : rev39_s0_lr.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane24 rev39_vertex3 rev39_vertex0 rev39_s0_lr
    rev39_vertex3_mem rev39_vertex0_mem (by decide)
def rev39_s0_ul : FractionPoint := ⟨24667453203873571,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev39_s0_ul_mem : rev39_s0_ul.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane6 rev39_vertex3 rev39_vertex2 rev39_s0_ul
    rev39_vertex3_mem rev39_vertex2_mem (by decide)
def rev39_s0_ur : FractionPoint := ⟨2017556719765051,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev39_s0_ur_mem : rev39_s0_ur.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane6 rev39_vertex3 rev39_vertex2 rev39_s0_ur
    rev39_vertex3_mem rev39_vertex2_mem (by decide)
theorem rev39_slab0 (p : Point) (hp : p∈IntegerCarrier rev39_planes)
    (hx0 : rev39_s0_ll.real.1≤p.1) (hx1 : p.1≤rev39_s0_lr.real.1) :
    p∈rationalHull (fractionRow39.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev39_plane24 rev39_plane6 rev39_s0_ll rev39_s0_lr rev39_s0_ul rev39_s0_ur
    (by decide) rev39_s0_ll_mem rev39_s0_lr_mem rev39_s0_ul_mem rev39_s0_ur_mem p
    (hp _ rev39_plane24_mem) (hp _ rev39_plane6_mem) hx0 hx1
def rev39_s1_ll : FractionPoint := ⟨2017556719765051,2631538706000000,43573950684930384731,189486049756494800000⟩
theorem rev39_s1_ll_mem : rev39_s1_ll.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane24 rev39_vertex3 rev39_vertex0 rev39_s1_ll
    rev39_vertex3_mem rev39_vertex0_mem (by decide)
def rev39_s1_lr : FractionPoint := ⟨28419630852349427,37052714692000000,87828936986982865489,381144337652744800000⟩
theorem rev39_s1_lr_mem : rev39_s1_lr.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane24 rev39_vertex3 rev39_vertex0 rev39_s1_lr
    rev39_vertex3_mem rev39_vertex0_mem (by decide)
def rev39_s1_ul : FractionPoint := ⟨2017556719765051,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev39_s1_ul_mem : rev39_s1_ul.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane54 rev39_vertex2 rev39_vertex1 rev39_s1_ul
    rev39_vertex2_mem rev39_vertex1_mem (by decide)
def rev39_s1_ur : FractionPoint := ⟨28419630852349427,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev39_s1_ur_mem : rev39_s1_ur.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane54 rev39_vertex2 rev39_vertex1 rev39_s1_ur
    rev39_vertex2_mem rev39_vertex1_mem (by decide)
theorem rev39_slab1 (p : Point) (hp : p∈IntegerCarrier rev39_planes)
    (hx0 : rev39_s1_ll.real.1≤p.1) (hx1 : p.1≤rev39_s1_lr.real.1) :
    p∈rationalHull (fractionRow39.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev39_plane24 rev39_plane54 rev39_s1_ll rev39_s1_lr rev39_s1_ul rev39_s1_ur
    (by decide) rev39_s1_ll_mem rev39_s1_lr_mem rev39_s1_ul_mem rev39_s1_ur_mem p
    (hp _ rev39_plane24_mem) (hp _ rev39_plane54_mem) hx0 hx1
def rev39_s2_ll : FractionPoint := ⟨28419630852349427,37052714692000000,87828936986982865489,381144337652744800000⟩
theorem rev39_s2_ll_mem : rev39_s2_ll.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane24 rev39_vertex3 rev39_vertex0 rev39_s2_ll
    rev39_vertex3_mem rev39_vertex0_mem (by decide)
def rev39_s2_lr : FractionPoint := ⟨816645038392619867,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev39_s2_lr_mem : rev39_s2_lr.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane24 rev39_vertex3 rev39_vertex0 rev39_s2_lr
    rev39_vertex3_mem rev39_vertex0_mem (by decide)
def rev39_s2_ul : FractionPoint := ⟨28419630852349427,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev39_s2_ul_mem : rev39_s2_ul.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane11 rev39_vertex1 rev39_vertex0 rev39_s2_ul
    rev39_vertex1_mem rev39_vertex0_mem (by decide)
def rev39_s2_ur : FractionPoint := ⟨816645038392619867,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev39_s2_ur_mem : rev39_s2_ur.real ∈ rationalHull (fractionRow39.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow39 rev39_plane11 rev39_vertex1 rev39_vertex0 rev39_s2_ur
    rev39_vertex1_mem rev39_vertex0_mem (by decide)
theorem rev39_slab2 (p : Point) (hp : p∈IntegerCarrier rev39_planes)
    (hx0 : rev39_s2_ll.real.1≤p.1) (hx1 : p.1≤rev39_s2_lr.real.1) :
    p∈rationalHull (fractionRow39.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev39_plane24 rev39_plane11 rev39_s2_ll rev39_s2_lr rev39_s2_ul rev39_s2_ur
    (by decide) rev39_s2_ll_mem rev39_s2_lr_mem rev39_s2_ul_mem rev39_s2_ur_mem p
    (hp _ rev39_plane24_mem) (hp _ rev39_plane11_mem) hx0 hx1
theorem rev39_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev39_planes) : rev39_s0_ll.real.1≤p.1 := by
  have hc := rev39_plane6.combine_sound rev39_plane24 1440116000000 287616000000 (by decide) (by decide) p
    (hp _ rev39_plane6_mem) (hp _ rev39_plane24_mem)
  exact (rev39_plane6.combine rev39_plane24 1440116000000 287616000000).xBoundCheck_sound rev39_s0_ll.nx rev39_s0_ll.dx true (by decide) p hc
theorem rev39_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev39_planes) : p.1≤rev39_s2_lr.real.1 := by
  have hc := rev39_plane11.combine_sound rev39_plane24 1440116000000 1861776000000 (by decide) (by decide) p
    (hp _ rev39_plane11_mem) (hp _ rev39_plane24_mem)
  exact (rev39_plane11.combine rev39_plane24 1440116000000 1861776000000).xBoundCheck_sound rev39_s2_lr.nx rev39_s2_lr.dx false (by decide) p hc
theorem rev39_hull (p : Point) (hp : p∈IntegerCarrier rev39_planes) :
    p∈rationalHull (fractionRow39.map FractionPoint.rational) := by
  have hxlo := rev39_bound0_lo p hp
  have hxhi := rev39_bound0_hi p hp
  by_cases h0 : p.1≤rev39_s0_lr.real.1
  · exact rev39_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev39_s1_lr.real.1
  · exact rev39_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev39_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull39 (p : Point)
    (hp : ∀ g, ClosedCell ((![3,5,15,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow39 := by
  rw [← fractionRow39_correct]
  exact rev39_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull39
