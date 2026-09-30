import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks13
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev106_planes : List IntegerPlane := integerOverlayPlanes ![7,5,10,8]
def rev106_plane6 : IntegerPlane := ⟨(-2058052000000),(-1574160000000),(-1942047499047)⟩
theorem rev106_plane6_mem : rev106_plane6 ∈ rev106_planes := by decide
def rev106_plane7 : IntegerPlane := ⟨(-202532000000),(-1861776000000),(-585903739447)⟩
theorem rev106_plane7_mem : rev106_plane7 ∈ rev106_planes := by decide
def rev106_plane24 : IntegerPlane := ⟨2129316000000,(-1440116000000),1301343880216⟩
theorem rev106_plane24_mem : rev106_plane24 ∈ rev106_planes := by decide
def rev106_plane59 : IntegerPlane := ⟨1440116000000,(-2129316000000),612143880216⟩
theorem rev106_plane59_mem : rev106_plane59 ∈ rev106_planes := by decide
def rev106_plane76 : IntegerPlane := ⟨1861776000000,202532000000,1478404260553⟩
theorem rev106_plane76_mem : rev106_plane76 ∈ rev106_planes := by decide
def rev106_plane77 : IntegerPlane := ⟨1574160000000,2058052000000,1690164500953⟩
theorem rev106_plane77_mem : rev106_plane77 ∈ rev106_planes := by decide
def rev106_vertex0 : FractionPoint := fractionRow106[0]!
theorem rev106_vertex0_mem : rev106_vertex0∈fractionRow106 := by decide
def rev106_vertex1 : FractionPoint := fractionRow106[1]!
theorem rev106_vertex1_mem : rev106_vertex1∈fractionRow106 := by decide
def rev106_vertex2 : FractionPoint := fractionRow106[2]!
theorem rev106_vertex2_mem : rev106_vertex2∈fractionRow106 := by decide
def rev106_vertex3 : FractionPoint := fractionRow106[3]!
theorem rev106_vertex3_mem : rev106_vertex3∈fractionRow106 := by decide
def rev106_vertex4 : FractionPoint := fractionRow106[4]!
theorem rev106_vertex4_mem : rev106_vertex4∈fractionRow106 := by decide
def rev106_vertex5 : FractionPoint := fractionRow106[5]!
theorem rev106_vertex5_mem : rev106_vertex5∈fractionRow106 := by decide
def rev106_s0_ll : FractionPoint := ⟨367887499047,483892000000,116004500953,483892000000⟩
theorem rev106_s0_ll_mem : rev106_s0_ll.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane6 rev106_vertex0 rev106_vertex1 rev106_s0_ll
    rev106_vertex0_mem rev106_vertex1_mem (by decide)
def rev106_s0_lr : FractionPoint := ⟨1001990771613779,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev106_s0_lr_mem : rev106_s0_lr.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane6 rev106_vertex0 rev106_vertex1 rev106_s0_lr
    rev106_vertex0_mem rev106_vertex1_mem (by decide)
def rev106_s0_ul : FractionPoint := ⟨367887499047,483892000000,116004500953,483892000000⟩
theorem rev106_s0_ul_mem : rev106_s0_ul.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane77 rev106_vertex0 rev106_vertex5 rev106_s0_ul
    rev106_vertex0_mem rev106_vertex5_mem (by decide)
def rev106_s0_ur : FractionPoint := ⟨1001990771613779,1306850464000000,39468654328950633847,168097888196008000000⟩
theorem rev106_s0_ur_mem : rev106_s0_ur.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane77 rev106_vertex0 rev106_vertex5 rev106_s0_ur
    rev106_vertex0_mem rev106_vertex5_mem (by decide)
theorem rev106_slab0 (p : Point) (hp : p∈IntegerCarrier rev106_planes)
    (hx0 : rev106_s0_ll.real.1≤p.1) (hx1 : p.1≤rev106_s0_lr.real.1) :
    p∈rationalHull (fractionRow106.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev106_plane6 rev106_plane77 rev106_s0_ll rev106_s0_lr rev106_s0_ul rev106_s0_ur
    (by decide) rev106_s0_ll_mem rev106_s0_lr_mem rev106_s0_ul_mem rev106_s0_ur_mem p
    (hp _ rev106_plane6_mem) (hp _ rev106_plane77_mem) hx0 hx1
def rev106_s1_ll : FractionPoint := ⟨1001990771613779,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev106_s1_ll_mem : rev106_s1_ll.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane7 rev106_vertex1 rev106_vertex2 rev106_s1_ll
    rev106_vertex1_mem rev106_vertex2_mem (by decide)
def rev106_s1_lr : FractionPoint := ⟨28419630852349427,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev106_s1_lr_mem : rev106_s1_lr.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane7 rev106_vertex1 rev106_vertex2 rev106_s1_lr
    rev106_vertex1_mem rev106_vertex2_mem (by decide)
def rev106_s1_ul : FractionPoint := ⟨1001990771613779,1306850464000000,39468654328950633847,168097888196008000000⟩
theorem rev106_s1_ul_mem : rev106_s1_ul.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane77 rev106_vertex0 rev106_vertex5 rev106_s1_ul
    rev106_vertex0_mem rev106_vertex5_mem (by decide)
def rev106_s1_ur : FractionPoint := ⟨28419630852349427,37052714692000000,638862033350846324827,2723443342046428000000⟩
theorem rev106_s1_ur_mem : rev106_s1_ur.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane77 rev106_vertex0 rev106_vertex5 rev106_s1_ur
    rev106_vertex0_mem rev106_vertex5_mem (by decide)
theorem rev106_slab1 (p : Point) (hp : p∈IntegerCarrier rev106_planes)
    (hx0 : rev106_s1_ll.real.1≤p.1) (hx1 : p.1≤rev106_s1_lr.real.1) :
    p∈rationalHull (fractionRow106.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev106_plane7 rev106_plane77 rev106_s1_ll rev106_s1_lr rev106_s1_ul rev106_s1_ur
    (by decide) rev106_s1_ll_mem rev106_s1_lr_mem rev106_s1_ul_mem rev106_s1_ur_mem p
    (hp _ rev106_plane7_mem) (hp _ rev106_plane77_mem) hx0 hx1
def rev106_s2_ll : FractionPoint := ⟨28419630852349427,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev106_s2_ll_mem : rev106_s2_ll.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane59 rev106_vertex2 rev106_vertex3 rev106_s2_ll
    rev106_vertex2_mem rev106_vertex3_mem (by decide)
def rev106_s2_lr : FractionPoint := ⟨342682485027,446179000000,103496514973,446179000000⟩
theorem rev106_s2_lr_mem : rev106_s2_lr.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane59 rev106_vertex2 rev106_vertex3 rev106_s2_lr
    rev106_vertex2_mem rev106_vertex3_mem (by decide)
def rev106_s2_ul : FractionPoint := ⟨28419630852349427,37052714692000000,638862033350846324827,2723443342046428000000⟩
theorem rev106_s2_ul_mem : rev106_s2_ul.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane77 rev106_vertex0 rev106_vertex5 rev106_s2_ul
    rev106_vertex0_mem rev106_vertex5_mem (by decide)
def rev106_s2_ur : FractionPoint := ⟨342682485027,446179000000,214678846240606267,918259583308000000⟩
theorem rev106_s2_ur_mem : rev106_s2_ur.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane77 rev106_vertex0 rev106_vertex5 rev106_s2_ur
    rev106_vertex0_mem rev106_vertex5_mem (by decide)
theorem rev106_slab2 (p : Point) (hp : p∈IntegerCarrier rev106_planes)
    (hx0 : rev106_s2_ll.real.1≤p.1) (hx1 : p.1≤rev106_s2_lr.real.1) :
    p∈rationalHull (fractionRow106.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev106_plane59 rev106_plane77 rev106_s2_ll rev106_s2_lr rev106_s2_ul rev106_s2_ur
    (by decide) rev106_s2_ll_mem rev106_s2_lr_mem rev106_s2_ul_mem rev106_s2_ur_mem p
    (hp _ rev106_plane59_mem) (hp _ rev106_plane77_mem) hx0 hx1
def rev106_s3_ll : FractionPoint := ⟨342682485027,446179000000,103496514973,446179000000⟩
theorem rev106_s3_ll_mem : rev106_s3_ll.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane24 rev106_vertex3 rev106_vertex4 rev106_s3_ll
    rev106_vertex3_mem rev106_vertex4_mem (by decide)
def rev106_s3_lr : FractionPoint := ⟨16877002803328811,21955087795200000,438413866624070129971,1882016262813824000000⟩
theorem rev106_s3_lr_mem : rev106_s3_lr.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane24 rev106_vertex3 rev106_vertex4 rev106_s3_lr
    rev106_vertex3_mem rev106_vertex4_mem (by decide)
def rev106_s3_ul : FractionPoint := ⟨342682485027,446179000000,214678846240606267,918259583308000000⟩
theorem rev106_s3_ul_mem : rev106_s3_ul.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane77 rev106_vertex0 rev106_vertex5 rev106_s3_ul
    rev106_vertex0_mem rev106_vertex5_mem (by decide)
def rev106_s3_ur : FractionPoint := ⟨16877002803328811,21955087795200000,304859692386221,1306850464000000⟩
theorem rev106_s3_ur_mem : rev106_s3_ur.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane77 rev106_vertex0 rev106_vertex5 rev106_s3_ur
    rev106_vertex0_mem rev106_vertex5_mem (by decide)
theorem rev106_slab3 (p : Point) (hp : p∈IntegerCarrier rev106_planes)
    (hx0 : rev106_s3_ll.real.1≤p.1) (hx1 : p.1≤rev106_s3_lr.real.1) :
    p∈rationalHull (fractionRow106.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev106_plane24 rev106_plane77 rev106_s3_ll rev106_s3_lr rev106_s3_ul rev106_s3_ur
    (by decide) rev106_s3_ll_mem rev106_s3_lr_mem rev106_s3_ul_mem rev106_s3_ur_mem p
    (hp _ rev106_plane24_mem) (hp _ rev106_plane77_mem) hx0 hx1
def rev106_s4_ll : FractionPoint := ⟨16877002803328811,21955087795200000,438413866624070129971,1882016262813824000000⟩
theorem rev106_s4_ll_mem : rev106_s4_ll.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane24 rev106_vertex3 rev106_vertex4 rev106_s4_ll
    rev106_vertex3_mem rev106_vertex4_mem (by decide)
def rev106_s4_lr : FractionPoint := ⟨119631870441922553,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev106_s4_lr_mem : rev106_s4_lr.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane24 rev106_vertex3 rev106_vertex4 rev106_s4_lr
    rev106_vertex3_mem rev106_vertex4_mem (by decide)
def rev106_s4_ul : FractionPoint := ⟨16877002803328811,21955087795200000,304859692386221,1306850464000000⟩
theorem rev106_s4_ul_mem : rev106_s4_ul.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane76 rev106_vertex5 rev106_vertex4 rev106_s4_ul
    rev106_vertex5_mem rev106_vertex4_mem (by decide)
def rev106_s4_ur : FractionPoint := ⟨119631870441922553,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev106_s4_ur_mem : rev106_s4_ur.real ∈ rationalHull (fractionRow106.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow106 rev106_plane76 rev106_vertex5 rev106_vertex4 rev106_s4_ur
    rev106_vertex5_mem rev106_vertex4_mem (by decide)
theorem rev106_slab4 (p : Point) (hp : p∈IntegerCarrier rev106_planes)
    (hx0 : rev106_s4_ll.real.1≤p.1) (hx1 : p.1≤rev106_s4_lr.real.1) :
    p∈rationalHull (fractionRow106.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev106_plane24 rev106_plane76 rev106_s4_ll rev106_s4_lr rev106_s4_ul rev106_s4_ur
    (by decide) rev106_s4_ll_mem rev106_s4_lr_mem rev106_s4_ul_mem rev106_s4_ur_mem p
    (hp _ rev106_plane24_mem) (hp _ rev106_plane76_mem) hx0 hx1
theorem rev106_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev106_planes) : rev106_s0_ll.real.1≤p.1 := by
  have hc := rev106_plane6.combine_sound rev106_plane77 2058052000000 1574160000000 (by decide) (by decide) p
    (hp _ rev106_plane6_mem) (hp _ rev106_plane77_mem)
  exact (rev106_plane6.combine rev106_plane77 2058052000000 1574160000000).xBoundCheck_sound rev106_s0_ll.nx rev106_s0_ll.dx true (by decide) p hc
theorem rev106_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev106_planes) : p.1≤rev106_s4_lr.real.1 := by
  have hc := rev106_plane24.combine_sound rev106_plane76 202532000000 1440116000000 (by decide) (by decide) p
    (hp _ rev106_plane24_mem) (hp _ rev106_plane76_mem)
  exact (rev106_plane24.combine rev106_plane76 202532000000 1440116000000).xBoundCheck_sound rev106_s4_lr.nx rev106_s4_lr.dx false (by decide) p hc
theorem rev106_hull (p : Point) (hp : p∈IntegerCarrier rev106_planes) :
    p∈rationalHull (fractionRow106.map FractionPoint.rational) := by
  have hxlo := rev106_bound0_lo p hp
  have hxhi := rev106_bound0_hi p hp
  by_cases h0 : p.1≤rev106_s0_lr.real.1
  · exact rev106_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev106_s1_lr.real.1
  · exact rev106_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev106_s2_lr.real.1
  · exact rev106_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev106_s3_lr.real.1
  · exact rev106_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev106_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull106 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,5,10,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow106 := by
  rw [← fractionRow106_correct]
  exact rev106_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull106
