import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks9
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev74_planes : List IntegerPlane := integerOverlayPlanes ![5,7,7,5]
def rev74_plane4 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-827972119784)⟩
theorem rev74_plane4_mem : rev74_plane4 ∈ rev74_planes := by decide
def rev74_plane26 : IntegerPlane := ⟨2058052000000,(-1574160000000),116004500953⟩
theorem rev74_plane26_mem : rev74_plane26 ∈ rev74_planes := by decide
def rev74_plane27 : IntegerPlane := ⟨202532000000,(-1861776000000),(-383371739447)⟩
theorem rev74_plane27_mem : rev74_plane27 ∈ rev74_planes := by decide
def rev74_plane46 : IntegerPlane := ⟨(-1574160000000),2058052000000,116004500953⟩
theorem rev74_plane46_mem : rev74_plane46 ∈ rev74_planes := by decide
def rev74_plane47 : IntegerPlane := ⟨(-1861776000000),202532000000,(-383371739447)⟩
theorem rev74_plane47_mem : rev74_plane47 ∈ rev74_planes := by decide
def rev74_plane64 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-827972119784)⟩
theorem rev74_plane64_mem : rev74_plane64 ∈ rev74_planes := by decide
def rev74_vertex0 : FractionPoint := fractionRow74[0]!
theorem rev74_vertex0_mem : rev74_vertex0∈fractionRow74 := by decide
def rev74_vertex1 : FractionPoint := fractionRow74[1]!
theorem rev74_vertex1_mem : rev74_vertex1∈fractionRow74 := by decide
def rev74_vertex2 : FractionPoint := fractionRow74[2]!
theorem rev74_vertex2_mem : rev74_vertex2∈fractionRow74 := by decide
def rev74_vertex3 : FractionPoint := fractionRow74[3]!
theorem rev74_vertex3_mem : rev74_vertex3∈fractionRow74 := by decide
def rev74_vertex4 : FractionPoint := fractionRow74[4]!
theorem rev74_vertex4_mem : rev74_vertex4∈fractionRow74 := by decide
def rev74_vertex5 : FractionPoint := fractionRow74[5]!
theorem rev74_vertex5_mem : rev74_vertex5∈fractionRow74 := by decide
def rev74_s0_ll : FractionPoint := ⟨35989531264477447,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev74_s0_ll_mem : rev74_s0_ll.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane4 rev74_vertex0 rev74_vertex1 rev74_s0_ll
    rev74_vertex0_mem rev74_vertex1_mem (by decide)
def rev74_s0_lr : FractionPoint := ⟨5078084991871189,21955087795200000,438413866624070129971,1882016262813824000000⟩
theorem rev74_s0_lr_mem : rev74_s0_lr.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane4 rev74_vertex0 rev74_vertex1 rev74_s0_lr
    rev74_vertex0_mem rev74_vertex1_mem (by decide)
def rev74_s0_ul : FractionPoint := ⟨35989531264477447,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev74_s0_ul_mem : rev74_s0_ul.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane47 rev74_vertex0 rev74_vertex5 rev74_s0_ul
    rev74_vertex0_mem rev74_vertex5_mem (by decide)
def rev74_s0_ur : FractionPoint := ⟨5078084991871189,21955087795200000,304859692386221,1306850464000000⟩
theorem rev74_s0_ur_mem : rev74_s0_ur.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane47 rev74_vertex0 rev74_vertex5 rev74_s0_ur
    rev74_vertex0_mem rev74_vertex5_mem (by decide)
theorem rev74_slab0 (p : Point) (hp : p∈IntegerCarrier rev74_planes)
    (hx0 : rev74_s0_ll.real.1≤p.1) (hx1 : p.1≤rev74_s0_lr.real.1) :
    p∈rationalHull (fractionRow74.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev74_plane4 rev74_plane47 rev74_s0_ll rev74_s0_lr rev74_s0_ul rev74_s0_ur
    (by decide) rev74_s0_ll_mem rev74_s0_lr_mem rev74_s0_ul_mem rev74_s0_ur_mem p
    (hp _ rev74_plane4_mem) (hp _ rev74_plane47_mem) hx0 hx1
def rev74_s1_ll : FractionPoint := ⟨5078084991871189,21955087795200000,438413866624070129971,1882016262813824000000⟩
theorem rev74_s1_ll_mem : rev74_s1_ll.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane4 rev74_vertex0 rev74_vertex1 rev74_s1_ll
    rev74_vertex0_mem rev74_vertex1_mem (by decide)
def rev74_s1_lr : FractionPoint := ⟨103496514973,446179000000,103496514973,446179000000⟩
theorem rev74_s1_lr_mem : rev74_s1_lr.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane4 rev74_vertex0 rev74_vertex1 rev74_s1_lr
    rev74_vertex0_mem rev74_vertex1_mem (by decide)
def rev74_s1_ul : FractionPoint := ⟨5078084991871189,21955087795200000,304859692386221,1306850464000000⟩
theorem rev74_s1_ul_mem : rev74_s1_ul.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane46 rev74_vertex5 rev74_vertex4 rev74_s1_ul
    rev74_vertex5_mem rev74_vertex4_mem (by decide)
def rev74_s1_ur : FractionPoint := ⟨103496514973,446179000000,214678846240606267,918259583308000000⟩
theorem rev74_s1_ur_mem : rev74_s1_ur.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane46 rev74_vertex5 rev74_vertex4 rev74_s1_ur
    rev74_vertex5_mem rev74_vertex4_mem (by decide)
theorem rev74_slab1 (p : Point) (hp : p∈IntegerCarrier rev74_planes)
    (hx0 : rev74_s1_ll.real.1≤p.1) (hx1 : p.1≤rev74_s1_lr.real.1) :
    p∈rationalHull (fractionRow74.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev74_plane4 rev74_plane46 rev74_s1_ll rev74_s1_lr rev74_s1_ul rev74_s1_ur
    (by decide) rev74_s1_ll_mem rev74_s1_lr_mem rev74_s1_ul_mem rev74_s1_ur_mem p
    (hp _ rev74_plane4_mem) (hp _ rev74_plane46_mem) hx0 hx1
def rev74_s2_ll : FractionPoint := ⟨103496514973,446179000000,103496514973,446179000000⟩
theorem rev74_s2_ll_mem : rev74_s2_ll.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane64 rev74_vertex1 rev74_vertex2 rev74_s2_ll
    rev74_vertex1_mem rev74_vertex2_mem (by decide)
def rev74_s2_lr : FractionPoint := ⟨8633083839650573,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev74_s2_lr_mem : rev74_s2_lr.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane64 rev74_vertex1 rev74_vertex2 rev74_s2_lr
    rev74_vertex1_mem rev74_vertex2_mem (by decide)
def rev74_s2_ul : FractionPoint := ⟨103496514973,446179000000,214678846240606267,918259583308000000⟩
theorem rev74_s2_ul_mem : rev74_s2_ul.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane46 rev74_vertex5 rev74_vertex4 rev74_s2_ul
    rev74_vertex5_mem rev74_vertex4_mem (by decide)
def rev74_s2_ur : FractionPoint := ⟨8633083839650573,37052714692000000,638862033350846324827,2723443342046428000000⟩
theorem rev74_s2_ur_mem : rev74_s2_ur.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane46 rev74_vertex5 rev74_vertex4 rev74_s2_ur
    rev74_vertex5_mem rev74_vertex4_mem (by decide)
theorem rev74_slab2 (p : Point) (hp : p∈IntegerCarrier rev74_planes)
    (hx0 : rev74_s2_ll.real.1≤p.1) (hx1 : p.1≤rev74_s2_lr.real.1) :
    p∈rationalHull (fractionRow74.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev74_plane64 rev74_plane46 rev74_s2_ll rev74_s2_lr rev74_s2_ul rev74_s2_ur
    (by decide) rev74_s2_ll_mem rev74_s2_lr_mem rev74_s2_ul_mem rev74_s2_ur_mem p
    (hp _ rev74_plane64_mem) (hp _ rev74_plane46_mem) hx0 hx1
def rev74_s3_ll : FractionPoint := ⟨8633083839650573,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev74_s3_ll_mem : rev74_s3_ll.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane27 rev74_vertex2 rev74_vertex3 rev74_s3_ll
    rev74_vertex2_mem rev74_vertex3_mem (by decide)
def rev74_s3_lr : FractionPoint := ⟨304859692386221,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev74_s3_lr_mem : rev74_s3_lr.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane27 rev74_vertex2 rev74_vertex3 rev74_s3_lr
    rev74_vertex2_mem rev74_vertex3_mem (by decide)
def rev74_s3_ul : FractionPoint := ⟨8633083839650573,37052714692000000,638862033350846324827,2723443342046428000000⟩
theorem rev74_s3_ul_mem : rev74_s3_ul.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane46 rev74_vertex5 rev74_vertex4 rev74_s3_ul
    rev74_vertex5_mem rev74_vertex4_mem (by decide)
def rev74_s3_ur : FractionPoint := ⟨304859692386221,1306850464000000,39468654328950633847,168097888196008000000⟩
theorem rev74_s3_ur_mem : rev74_s3_ur.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane46 rev74_vertex5 rev74_vertex4 rev74_s3_ur
    rev74_vertex5_mem rev74_vertex4_mem (by decide)
theorem rev74_slab3 (p : Point) (hp : p∈IntegerCarrier rev74_planes)
    (hx0 : rev74_s3_ll.real.1≤p.1) (hx1 : p.1≤rev74_s3_lr.real.1) :
    p∈rationalHull (fractionRow74.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev74_plane27 rev74_plane46 rev74_s3_ll rev74_s3_lr rev74_s3_ul rev74_s3_ur
    (by decide) rev74_s3_ll_mem rev74_s3_lr_mem rev74_s3_ul_mem rev74_s3_ur_mem p
    (hp _ rev74_plane27_mem) (hp _ rev74_plane46_mem) hx0 hx1
def rev74_s4_ll : FractionPoint := ⟨304859692386221,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev74_s4_ll_mem : rev74_s4_ll.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane26 rev74_vertex3 rev74_vertex4 rev74_s4_ll
    rev74_vertex3_mem rev74_vertex4_mem (by decide)
def rev74_s4_lr : FractionPoint := ⟨116004500953,483892000000,116004500953,483892000000⟩
theorem rev74_s4_lr_mem : rev74_s4_lr.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane26 rev74_vertex3 rev74_vertex4 rev74_s4_lr
    rev74_vertex3_mem rev74_vertex4_mem (by decide)
def rev74_s4_ul : FractionPoint := ⟨304859692386221,1306850464000000,39468654328950633847,168097888196008000000⟩
theorem rev74_s4_ul_mem : rev74_s4_ul.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane46 rev74_vertex5 rev74_vertex4 rev74_s4_ul
    rev74_vertex5_mem rev74_vertex4_mem (by decide)
def rev74_s4_ur : FractionPoint := ⟨116004500953,483892000000,116004500953,483892000000⟩
theorem rev74_s4_ur_mem : rev74_s4_ur.real ∈ rationalHull (fractionRow74.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow74 rev74_plane46 rev74_vertex5 rev74_vertex4 rev74_s4_ur
    rev74_vertex5_mem rev74_vertex4_mem (by decide)
theorem rev74_slab4 (p : Point) (hp : p∈IntegerCarrier rev74_planes)
    (hx0 : rev74_s4_ll.real.1≤p.1) (hx1 : p.1≤rev74_s4_lr.real.1) :
    p∈rationalHull (fractionRow74.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev74_plane26 rev74_plane46 rev74_s4_ll rev74_s4_lr rev74_s4_ul rev74_s4_ur
    (by decide) rev74_s4_ll_mem rev74_s4_lr_mem rev74_s4_ul_mem rev74_s4_ur_mem p
    (hp _ rev74_plane26_mem) (hp _ rev74_plane46_mem) hx0 hx1
theorem rev74_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev74_planes) : rev74_s0_ll.real.1≤p.1 := by
  have hc := rev74_plane4.combine_sound rev74_plane47 202532000000 1440116000000 (by decide) (by decide) p
    (hp _ rev74_plane4_mem) (hp _ rev74_plane47_mem)
  exact (rev74_plane4.combine rev74_plane47 202532000000 1440116000000).xBoundCheck_sound rev74_s0_ll.nx rev74_s0_ll.dx true (by decide) p hc
theorem rev74_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev74_planes) : p.1≤rev74_s4_lr.real.1 := by
  have hc := rev74_plane26.combine_sound rev74_plane46 2058052000000 1574160000000 (by decide) (by decide) p
    (hp _ rev74_plane26_mem) (hp _ rev74_plane46_mem)
  exact (rev74_plane26.combine rev74_plane46 2058052000000 1574160000000).xBoundCheck_sound rev74_s4_lr.nx rev74_s4_lr.dx false (by decide) p hc
theorem rev74_hull (p : Point) (hp : p∈IntegerCarrier rev74_planes) :
    p∈rationalHull (fractionRow74.map FractionPoint.rational) := by
  have hxlo := rev74_bound0_lo p hp
  have hxhi := rev74_bound0_hi p hp
  by_cases h0 : p.1≤rev74_s0_lr.real.1
  · exact rev74_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev74_s1_lr.real.1
  · exact rev74_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev74_s2_lr.real.1
  · exact rev74_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev74_s3_lr.real.1
  · exact rev74_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev74_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull74 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,7,7,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow74 := by
  rw [← fractionRow74_correct]
  exact rev74_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull74
