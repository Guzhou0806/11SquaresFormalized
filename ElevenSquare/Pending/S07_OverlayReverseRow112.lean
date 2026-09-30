import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks14
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev112_planes : List IntegerPlane := integerOverlayPlanes ![8,10,5,3]
def rev112_plane39 : IntegerPlane := ⟨(-2129316000000),1440116000000,612143880216⟩
theorem rev112_plane39_mem : rev112_plane39 ∈ rev112_planes := by decide
def rev112_plane66 : IntegerPlane := ⟨287616000000,(-1855520000000),(-1356143759600)⟩
theorem rev112_plane66_mem : rev112_plane66 ∈ rev112_planes := by decide
def rev112_plane71 : IntegerPlane := ⟨1861776000000,202532000000,585903739447⟩
theorem rev112_plane71_mem : rev112_plane71 ∈ rev112_planes := by decide
def rev112_vertex0 : FractionPoint := fractionRow112[0]!
theorem rev112_vertex0_mem : rev112_vertex0∈fractionRow112 := by decide
def rev112_vertex1 : FractionPoint := fractionRow112[1]!
theorem rev112_vertex1_mem : rev112_vertex1∈fractionRow112 := by decide
def rev112_vertex2 : FractionPoint := fractionRow112[2]!
theorem rev112_vertex2_mem : rev112_vertex2∈fractionRow112 := by decide
def rev112_s0_ll : FractionPoint := ⟨2553622230880379,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev112_s0_ll_mem : rev112_s0_ll.real ∈ rationalHull (fractionRow112.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow112 rev112_plane66 rev112_vertex2 rev112_vertex0 rev112_s0_ll
    rev112_vertex2_mem rev112_vertex0_mem (by decide)
def rev112_s0_lr : FractionPoint := ⟨35989531264477447,155621401706400000,164729284083707661293,214850166141562000000⟩
theorem rev112_s0_lr_mem : rev112_s0_lr.real ∈ rationalHull (fractionRow112.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow112 rev112_plane66 rev112_vertex2 rev112_vertex0 rev112_s0_lr
    rev112_vertex2_mem rev112_vertex0_mem (by decide)
def rev112_s0_ul : FractionPoint := ⟨2553622230880379,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev112_s0_ul_mem : rev112_s0_ul.real ∈ rationalHull (fractionRow112.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow112 rev112_plane39 rev112_vertex2 rev112_vertex1 rev112_s0_ul
    rev112_vertex2_mem rev112_vertex1_mem (by decide)
def rev112_s0_ur : FractionPoint := ⟨35989531264477447,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev112_s0_ur_mem : rev112_s0_ur.real ∈ rationalHull (fractionRow112.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow112 rev112_plane39 rev112_vertex2 rev112_vertex1 rev112_s0_ur
    rev112_vertex2_mem rev112_vertex1_mem (by decide)
theorem rev112_slab0 (p : Point) (hp : p∈IntegerCarrier rev112_planes)
    (hx0 : rev112_s0_ll.real.1≤p.1) (hx1 : p.1≤rev112_s0_lr.real.1) :
    p∈rationalHull (fractionRow112.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev112_plane66 rev112_plane39 rev112_s0_ll rev112_s0_lr rev112_s0_ul rev112_s0_ur
    (by decide) rev112_s0_ll_mem rev112_s0_lr_mem rev112_s0_ul_mem rev112_s0_ur_mem p
    (hp _ rev112_plane66_mem) (hp _ rev112_plane39_mem) hx0 hx1
def rev112_s1_ll : FractionPoint := ⟨35989531264477447,155621401706400000,164729284083707661293,214850166141562000000⟩
theorem rev112_s1_ll_mem : rev112_s1_ll.real ∈ rationalHull (fractionRow112.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow112 rev112_plane66 rev112_vertex2 rev112_vertex0 rev112_s1_ll
    rev112_vertex2_mem rev112_vertex0_mem (by decide)
def rev112_s1_lr : FractionPoint := ⟨5078084991871189,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev112_s1_lr_mem : rev112_s1_lr.real ∈ rationalHull (fractionRow112.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow112 rev112_plane66 rev112_vertex2 rev112_vertex0 rev112_s1_lr
    rev112_vertex2_mem rev112_vertex0_mem (by decide)
def rev112_s1_ul : FractionPoint := ⟨35989531264477447,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev112_s1_ul_mem : rev112_s1_ul.real ∈ rationalHull (fractionRow112.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow112 rev112_plane71 rev112_vertex1 rev112_vertex0 rev112_s1_ul
    rev112_vertex1_mem rev112_vertex0_mem (by decide)
def rev112_s1_ur : FractionPoint := ⟨5078084991871189,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev112_s1_ur_mem : rev112_s1_ur.real ∈ rationalHull (fractionRow112.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow112 rev112_plane71 rev112_vertex1 rev112_vertex0 rev112_s1_ur
    rev112_vertex1_mem rev112_vertex0_mem (by decide)
theorem rev112_slab1 (p : Point) (hp : p∈IntegerCarrier rev112_planes)
    (hx0 : rev112_s1_ll.real.1≤p.1) (hx1 : p.1≤rev112_s1_lr.real.1) :
    p∈rationalHull (fractionRow112.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev112_plane66 rev112_plane71 rev112_s1_ll rev112_s1_lr rev112_s1_ul rev112_s1_ur
    (by decide) rev112_s1_ll_mem rev112_s1_lr_mem rev112_s1_ul_mem rev112_s1_ur_mem p
    (hp _ rev112_plane66_mem) (hp _ rev112_plane71_mem) hx0 hx1
theorem rev112_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev112_planes) : rev112_s0_ll.real.1≤p.1 := by
  have hc := rev112_plane39.combine_sound rev112_plane66 1855520000000 1440116000000 (by decide) (by decide) p
    (hp _ rev112_plane39_mem) (hp _ rev112_plane66_mem)
  exact (rev112_plane39.combine rev112_plane66 1855520000000 1440116000000).xBoundCheck_sound rev112_s0_ll.nx rev112_s0_ll.dx true (by decide) p hc
theorem rev112_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev112_planes) : p.1≤rev112_s1_lr.real.1 := by
  have hc := rev112_plane66.combine_sound rev112_plane71 202532000000 1855520000000 (by decide) (by decide) p
    (hp _ rev112_plane66_mem) (hp _ rev112_plane71_mem)
  exact (rev112_plane66.combine rev112_plane71 202532000000 1855520000000).xBoundCheck_sound rev112_s1_lr.nx rev112_s1_lr.dx false (by decide) p hc
theorem rev112_hull (p : Point) (hp : p∈IntegerCarrier rev112_planes) :
    p∈rationalHull (fractionRow112.map FractionPoint.rational) := by
  have hxlo := rev112_bound0_lo p hp
  have hxhi := rev112_bound0_hi p hp
  by_cases h0 : p.1≤rev112_s0_lr.real.1
  · exact rev112_slab0 p hp hxlo h0
  exact rev112_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull112 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,10,5,3] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow112 := by
  rw [← fractionRow112_correct]
  exact rev112_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull112
