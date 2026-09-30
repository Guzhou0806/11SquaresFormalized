import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks14
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev113_planes : List IntegerPlane := integerOverlayPlanes ![8,10,5,7]
def rev113_plane16 : IntegerPlane := ⟨202532000000,1861776000000,1478404260553⟩
theorem rev113_plane16_mem : rev113_plane16 ∈ rev113_planes := by decide
def rev113_plane17 : IntegerPlane := ⟨2058052000000,1574160000000,1690164500953⟩
theorem rev113_plane17_mem : rev113_plane17 ∈ rev113_planes := by decide
def rev113_plane39 : IntegerPlane := ⟨(-2129316000000),1440116000000,612143880216⟩
theorem rev113_plane39_mem : rev113_plane39 ∈ rev113_planes := by decide
def rev113_plane44 : IntegerPlane := ⟨(-1440116000000),2129316000000,1301343880216⟩
theorem rev113_plane44_mem : rev113_plane44 ∈ rev113_planes := by decide
def rev113_plane66 : IntegerPlane := ⟨(-1574160000000),(-2058052000000),(-1942047499047)⟩
theorem rev113_plane66_mem : rev113_plane66 ∈ rev113_planes := by decide
def rev113_plane67 : IntegerPlane := ⟨(-1861776000000),(-202532000000),(-585903739447)⟩
theorem rev113_plane67_mem : rev113_plane67 ∈ rev113_planes := by decide
def rev113_vertex0 : FractionPoint := fractionRow113[0]!
theorem rev113_vertex0_mem : rev113_vertex0∈fractionRow113 := by decide
def rev113_vertex1 : FractionPoint := fractionRow113[1]!
theorem rev113_vertex1_mem : rev113_vertex1∈fractionRow113 := by decide
def rev113_vertex2 : FractionPoint := fractionRow113[2]!
theorem rev113_vertex2_mem : rev113_vertex2∈fractionRow113 := by decide
def rev113_vertex3 : FractionPoint := fractionRow113[3]!
theorem rev113_vertex3_mem : rev113_vertex3∈fractionRow113 := by decide
def rev113_vertex4 : FractionPoint := fractionRow113[4]!
theorem rev113_vertex4_mem : rev113_vertex4∈fractionRow113 := by decide
def rev113_vertex5 : FractionPoint := fractionRow113[5]!
theorem rev113_vertex5_mem : rev113_vertex5∈fractionRow113 := by decide
def rev113_s0_ll : FractionPoint := ⟨35989531264477447,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev113_s0_ll_mem : rev113_s0_ll.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane67 rev113_vertex4 rev113_vertex5 rev113_s0_ll
    rev113_vertex4_mem rev113_vertex5_mem (by decide)
def rev113_s0_lr : FractionPoint := ⟨5078084991871189,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev113_s0_lr_mem : rev113_s0_lr.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane67 rev113_vertex4 rev113_vertex5 rev113_s0_lr
    rev113_vertex4_mem rev113_vertex5_mem (by decide)
def rev113_s0_ul : FractionPoint := ⟨35989531264477447,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev113_s0_ul_mem : rev113_s0_ul.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane39 rev113_vertex4 rev113_vertex3 rev113_s0_ul
    rev113_vertex4_mem rev113_vertex3_mem (by decide)
def rev113_s0_ur : FractionPoint := ⟨5078084991871189,21955087795200000,1443602396189753870029,1882016262813824000000⟩
theorem rev113_s0_ur_mem : rev113_s0_ur.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane39 rev113_vertex4 rev113_vertex3 rev113_s0_ur
    rev113_vertex4_mem rev113_vertex3_mem (by decide)
theorem rev113_slab0 (p : Point) (hp : p∈IntegerCarrier rev113_planes)
    (hx0 : rev113_s0_ll.real.1≤p.1) (hx1 : p.1≤rev113_s0_lr.real.1) :
    p∈rationalHull (fractionRow113.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev113_plane67 rev113_plane39 rev113_s0_ll rev113_s0_lr rev113_s0_ul rev113_s0_ur
    (by decide) rev113_s0_ll_mem rev113_s0_lr_mem rev113_s0_ul_mem rev113_s0_ur_mem p
    (hp _ rev113_plane67_mem) (hp _ rev113_plane39_mem) hx0 hx1
def rev113_s1_ll : FractionPoint := ⟨5078084991871189,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev113_s1_ll_mem : rev113_s1_ll.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane66 rev113_vertex5 rev113_vertex0 rev113_s1_ll
    rev113_vertex5_mem rev113_vertex0_mem (by decide)
def rev113_s1_lr : FractionPoint := ⟨103496514973,446179000000,703580737067393733,918259583308000000⟩
theorem rev113_s1_lr_mem : rev113_s1_lr.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane66 rev113_vertex5 rev113_vertex0 rev113_s1_lr
    rev113_vertex5_mem rev113_vertex0_mem (by decide)
def rev113_s1_ul : FractionPoint := ⟨5078084991871189,21955087795200000,1443602396189753870029,1882016262813824000000⟩
theorem rev113_s1_ul_mem : rev113_s1_ul.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane39 rev113_vertex4 rev113_vertex3 rev113_s1_ul
    rev113_vertex4_mem rev113_vertex3_mem (by decide)
def rev113_s1_ur : FractionPoint := ⟨103496514973,446179000000,342682485027,446179000000⟩
theorem rev113_s1_ur_mem : rev113_s1_ur.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane39 rev113_vertex4 rev113_vertex3 rev113_s1_ur
    rev113_vertex4_mem rev113_vertex3_mem (by decide)
theorem rev113_slab1 (p : Point) (hp : p∈IntegerCarrier rev113_planes)
    (hx0 : rev113_s1_ll.real.1≤p.1) (hx1 : p.1≤rev113_s1_lr.real.1) :
    p∈rationalHull (fractionRow113.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev113_plane66 rev113_plane39 rev113_s1_ll rev113_s1_lr rev113_s1_ul rev113_s1_ur
    (by decide) rev113_s1_ll_mem rev113_s1_lr_mem rev113_s1_ul_mem rev113_s1_ur_mem p
    (hp _ rev113_plane66_mem) (hp _ rev113_plane39_mem) hx0 hx1
def rev113_s2_ll : FractionPoint := ⟨103496514973,446179000000,703580737067393733,918259583308000000⟩
theorem rev113_s2_ll_mem : rev113_s2_ll.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane66 rev113_vertex5 rev113_vertex0 rev113_s2_ll
    rev113_vertex5_mem rev113_vertex0_mem (by decide)
def rev113_s2_lr : FractionPoint := ⟨8633083839650573,37052714692000000,2084581308695581675173,2723443342046428000000⟩
theorem rev113_s2_lr_mem : rev113_s2_lr.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane66 rev113_vertex5 rev113_vertex0 rev113_s2_lr
    rev113_vertex5_mem rev113_vertex0_mem (by decide)
def rev113_s2_ul : FractionPoint := ⟨103496514973,446179000000,342682485027,446179000000⟩
theorem rev113_s2_ul_mem : rev113_s2_ul.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane44 rev113_vertex3 rev113_vertex2 rev113_s2_ul
    rev113_vertex3_mem rev113_vertex2_mem (by decide)
def rev113_s2_ur : FractionPoint := ⟨8633083839650573,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev113_s2_ur_mem : rev113_s2_ur.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane44 rev113_vertex3 rev113_vertex2 rev113_s2_ur
    rev113_vertex3_mem rev113_vertex2_mem (by decide)
theorem rev113_slab2 (p : Point) (hp : p∈IntegerCarrier rev113_planes)
    (hx0 : rev113_s2_ll.real.1≤p.1) (hx1 : p.1≤rev113_s2_lr.real.1) :
    p∈rationalHull (fractionRow113.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev113_plane66 rev113_plane44 rev113_s2_ll rev113_s2_lr rev113_s2_ul rev113_s2_ur
    (by decide) rev113_s2_ll_mem rev113_s2_lr_mem rev113_s2_ul_mem rev113_s2_ur_mem p
    (hp _ rev113_plane66_mem) (hp _ rev113_plane44_mem) hx0 hx1
def rev113_s3_ll : FractionPoint := ⟨8633083839650573,37052714692000000,2084581308695581675173,2723443342046428000000⟩
theorem rev113_s3_ll_mem : rev113_s3_ll.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane66 rev113_vertex5 rev113_vertex0 rev113_s3_ll
    rev113_vertex5_mem rev113_vertex0_mem (by decide)
def rev113_s3_lr : FractionPoint := ⟨304859692386221,1306850464000000,128629233867057366153,168097888196008000000⟩
theorem rev113_s3_lr_mem : rev113_s3_lr.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane66 rev113_vertex5 rev113_vertex0 rev113_s3_lr
    rev113_vertex5_mem rev113_vertex0_mem (by decide)
def rev113_s3_ul : FractionPoint := ⟨8633083839650573,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev113_s3_ul_mem : rev113_s3_ul.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane16 rev113_vertex2 rev113_vertex1 rev113_s3_ul
    rev113_vertex2_mem rev113_vertex1_mem (by decide)
def rev113_s3_ur : FractionPoint := ⟨304859692386221,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev113_s3_ur_mem : rev113_s3_ur.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane16 rev113_vertex2 rev113_vertex1 rev113_s3_ur
    rev113_vertex2_mem rev113_vertex1_mem (by decide)
theorem rev113_slab3 (p : Point) (hp : p∈IntegerCarrier rev113_planes)
    (hx0 : rev113_s3_ll.real.1≤p.1) (hx1 : p.1≤rev113_s3_lr.real.1) :
    p∈rationalHull (fractionRow113.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev113_plane66 rev113_plane16 rev113_s3_ll rev113_s3_lr rev113_s3_ul rev113_s3_ur
    (by decide) rev113_s3_ll_mem rev113_s3_lr_mem rev113_s3_ul_mem rev113_s3_ur_mem p
    (hp _ rev113_plane66_mem) (hp _ rev113_plane16_mem) hx0 hx1
def rev113_s4_ll : FractionPoint := ⟨304859692386221,1306850464000000,128629233867057366153,168097888196008000000⟩
theorem rev113_s4_ll_mem : rev113_s4_ll.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane66 rev113_vertex5 rev113_vertex0 rev113_s4_ll
    rev113_vertex5_mem rev113_vertex0_mem (by decide)
def rev113_s4_lr : FractionPoint := ⟨116004500953,483892000000,367887499047,483892000000⟩
theorem rev113_s4_lr_mem : rev113_s4_lr.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane66 rev113_vertex5 rev113_vertex0 rev113_s4_lr
    rev113_vertex5_mem rev113_vertex0_mem (by decide)
def rev113_s4_ul : FractionPoint := ⟨304859692386221,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev113_s4_ul_mem : rev113_s4_ul.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane17 rev113_vertex1 rev113_vertex0 rev113_s4_ul
    rev113_vertex1_mem rev113_vertex0_mem (by decide)
def rev113_s4_ur : FractionPoint := ⟨116004500953,483892000000,367887499047,483892000000⟩
theorem rev113_s4_ur_mem : rev113_s4_ur.real ∈ rationalHull (fractionRow113.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow113 rev113_plane17 rev113_vertex1 rev113_vertex0 rev113_s4_ur
    rev113_vertex1_mem rev113_vertex0_mem (by decide)
theorem rev113_slab4 (p : Point) (hp : p∈IntegerCarrier rev113_planes)
    (hx0 : rev113_s4_ll.real.1≤p.1) (hx1 : p.1≤rev113_s4_lr.real.1) :
    p∈rationalHull (fractionRow113.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev113_plane66 rev113_plane17 rev113_s4_ll rev113_s4_lr rev113_s4_ul rev113_s4_ur
    (by decide) rev113_s4_ll_mem rev113_s4_lr_mem rev113_s4_ul_mem rev113_s4_ur_mem p
    (hp _ rev113_plane66_mem) (hp _ rev113_plane17_mem) hx0 hx1
theorem rev113_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev113_planes) : rev113_s0_ll.real.1≤p.1 := by
  have hc := rev113_plane39.combine_sound rev113_plane67 202532000000 1440116000000 (by decide) (by decide) p
    (hp _ rev113_plane39_mem) (hp _ rev113_plane67_mem)
  exact (rev113_plane39.combine rev113_plane67 202532000000 1440116000000).xBoundCheck_sound rev113_s0_ll.nx rev113_s0_ll.dx true (by decide) p hc
theorem rev113_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev113_planes) : p.1≤rev113_s4_lr.real.1 := by
  have hc := rev113_plane17.combine_sound rev113_plane66 2058052000000 1574160000000 (by decide) (by decide) p
    (hp _ rev113_plane17_mem) (hp _ rev113_plane66_mem)
  exact (rev113_plane17.combine rev113_plane66 2058052000000 1574160000000).xBoundCheck_sound rev113_s4_lr.nx rev113_s4_lr.dx false (by decide) p hc
theorem rev113_hull (p : Point) (hp : p∈IntegerCarrier rev113_planes) :
    p∈rationalHull (fractionRow113.map FractionPoint.rational) := by
  have hxlo := rev113_bound0_lo p hp
  have hxhi := rev113_bound0_hi p hp
  by_cases h0 : p.1≤rev113_s0_lr.real.1
  · exact rev113_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev113_s1_lr.real.1
  · exact rev113_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev113_s2_lr.real.1
  · exact rev113_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev113_s3_lr.real.1
  · exact rev113_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev113_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull113 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,10,5,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow113 := by
  rw [← fractionRow113_correct]
  exact rev113_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull113
