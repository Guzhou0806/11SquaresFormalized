import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks13
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev109_planes : List IntegerPlane := integerOverlayPlanes ![7,5,15,8]
def rev109_plane7 : IntegerPlane := ⟨(-202532000000),(-1861776000000),(-585903739447)⟩
theorem rev109_plane7_mem : rev109_plane7 ∈ rev109_planes := by decide
def rev109_plane24 : IntegerPlane := ⟨2129316000000,(-1440116000000),1301343880216⟩
theorem rev109_plane24_mem : rev109_plane24 ∈ rev109_planes := by decide
def rev109_plane54 : IntegerPlane := ⟨(-1440116000000),2129316000000,(-612143880216)⟩
theorem rev109_plane54_mem : rev109_plane54 ∈ rev109_planes := by decide
def rev109_vertex0 : FractionPoint := fractionRow109[0]!
theorem rev109_vertex0_mem : rev109_vertex0∈fractionRow109 := by decide
def rev109_vertex1 : FractionPoint := fractionRow109[1]!
theorem rev109_vertex1_mem : rev109_vertex1∈fractionRow109 := by decide
def rev109_vertex2 : FractionPoint := fractionRow109[2]!
theorem rev109_vertex2_mem : rev109_vertex2∈fractionRow109 := by decide
def rev109_s0_ll : FractionPoint := ⟨28419630852349427,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev109_s0_ll_mem : rev109_s0_ll.real ∈ rationalHull (fractionRow109.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow109 rev109_plane7 rev109_vertex0 rev109_vertex1 rev109_s0_ll
    rev109_vertex0_mem rev109_vertex1_mem (by decide)
def rev109_s0_lr : FractionPoint := ⟨816645038392619867,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev109_s0_lr_mem : rev109_s0_lr.real ∈ rationalHull (fractionRow109.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow109 rev109_plane7 rev109_vertex0 rev109_vertex1 rev109_s0_lr
    rev109_vertex0_mem rev109_vertex1_mem (by decide)
def rev109_s0_ul : FractionPoint := ⟨28419630852349427,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev109_s0_ul_mem : rev109_s0_ul.real ∈ rationalHull (fractionRow109.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow109 rev109_plane54 rev109_vertex0 rev109_vertex2 rev109_s0_ul
    rev109_vertex0_mem rev109_vertex2_mem (by decide)
def rev109_s0_ur : FractionPoint := ⟨816645038392619867,1063994749732000000,26237285573971392314123,113279052226017165600000⟩
theorem rev109_s0_ur_mem : rev109_s0_ur.real ∈ rationalHull (fractionRow109.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow109 rev109_plane54 rev109_vertex0 rev109_vertex2 rev109_s0_ur
    rev109_vertex0_mem rev109_vertex2_mem (by decide)
theorem rev109_slab0 (p : Point) (hp : p∈IntegerCarrier rev109_planes)
    (hx0 : rev109_s0_ll.real.1≤p.1) (hx1 : p.1≤rev109_s0_lr.real.1) :
    p∈rationalHull (fractionRow109.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev109_plane7 rev109_plane54 rev109_s0_ll rev109_s0_lr rev109_s0_ul rev109_s0_ur
    (by decide) rev109_s0_ll_mem rev109_s0_lr_mem rev109_s0_ul_mem rev109_s0_ur_mem p
    (hp _ rev109_plane7_mem) (hp _ rev109_plane54_mem) hx0 hx1
def rev109_s1_ll : FractionPoint := ⟨816645038392619867,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev109_s1_ll_mem : rev109_s1_ll.real ∈ rationalHull (fractionRow109.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow109 rev109_plane24 rev109_vertex1 rev109_vertex2 rev109_s1_ll
    rev109_vertex1_mem rev109_vertex2_mem (by decide)
def rev109_s1_lr : FractionPoint := ⟨342682485027,446179000000,103496514973,446179000000⟩
theorem rev109_s1_lr_mem : rev109_s1_lr.real ∈ rationalHull (fractionRow109.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow109 rev109_plane24 rev109_vertex1 rev109_vertex2 rev109_s1_lr
    rev109_vertex1_mem rev109_vertex2_mem (by decide)
def rev109_s1_ul : FractionPoint := ⟨816645038392619867,1063994749732000000,26237285573971392314123,113279052226017165600000⟩
theorem rev109_s1_ul_mem : rev109_s1_ul.real ∈ rationalHull (fractionRow109.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow109 rev109_plane54 rev109_vertex0 rev109_vertex2 rev109_s1_ul
    rev109_vertex0_mem rev109_vertex2_mem (by decide)
def rev109_s1_ur : FractionPoint := ⟨342682485027,446179000000,103496514973,446179000000⟩
theorem rev109_s1_ur_mem : rev109_s1_ur.real ∈ rationalHull (fractionRow109.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow109 rev109_plane54 rev109_vertex0 rev109_vertex2 rev109_s1_ur
    rev109_vertex0_mem rev109_vertex2_mem (by decide)
theorem rev109_slab1 (p : Point) (hp : p∈IntegerCarrier rev109_planes)
    (hx0 : rev109_s1_ll.real.1≤p.1) (hx1 : p.1≤rev109_s1_lr.real.1) :
    p∈rationalHull (fractionRow109.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev109_plane24 rev109_plane54 rev109_s1_ll rev109_s1_lr rev109_s1_ul rev109_s1_ur
    (by decide) rev109_s1_ll_mem rev109_s1_lr_mem rev109_s1_ul_mem rev109_s1_ur_mem p
    (hp _ rev109_plane24_mem) (hp _ rev109_plane54_mem) hx0 hx1
theorem rev109_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev109_planes) : rev109_s0_ll.real.1≤p.1 := by
  have hc := rev109_plane7.combine_sound rev109_plane54 2129316000000 1861776000000 (by decide) (by decide) p
    (hp _ rev109_plane7_mem) (hp _ rev109_plane54_mem)
  exact (rev109_plane7.combine rev109_plane54 2129316000000 1861776000000).xBoundCheck_sound rev109_s0_ll.nx rev109_s0_ll.dx true (by decide) p hc
theorem rev109_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev109_planes) : p.1≤rev109_s1_lr.real.1 := by
  have hc := rev109_plane24.combine_sound rev109_plane54 2129316000000 1440116000000 (by decide) (by decide) p
    (hp _ rev109_plane24_mem) (hp _ rev109_plane54_mem)
  exact (rev109_plane24.combine rev109_plane54 2129316000000 1440116000000).xBoundCheck_sound rev109_s1_lr.nx rev109_s1_lr.dx false (by decide) p hc
theorem rev109_hull (p : Point) (hp : p∈IntegerCarrier rev109_planes) :
    p∈rationalHull (fractionRow109.map FractionPoint.rational) := by
  have hxlo := rev109_bound0_lo p hp
  have hxhi := rev109_bound0_hi p hp
  by_cases h0 : p.1≤rev109_s0_lr.real.1
  · exact rev109_slab0 p hp hxlo h0
  exact rev109_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull109 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,5,15,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow109 := by
  rw [← fractionRow109_correct]
  exact rev109_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull109
