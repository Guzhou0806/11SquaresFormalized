import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks18
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev145_planes : List IntegerPlane := integerOverlayPlanes ![10,8,8,10]
def rev145_plane19 : IntegerPlane := ⟨2129316000000,1440116000000,2741459880216⟩
theorem rev145_plane19_mem : rev145_plane19 ∈ rev145_planes := by decide
def rev145_plane36 : IntegerPlane := ⟨(-202532000000),1861776000000,1275872260553⟩
theorem rev145_plane36_mem : rev145_plane36 ∈ rev145_planes := by decide
def rev145_plane37 : IntegerPlane := ⟨(-2058052000000),1574160000000,(-367887499047)⟩
theorem rev145_plane37_mem : rev145_plane37 ∈ rev145_planes := by decide
def rev145_plane56 : IntegerPlane := ⟨1861776000000,(-202532000000),1275872260553⟩
theorem rev145_plane56_mem : rev145_plane56 ∈ rev145_planes := by decide
def rev145_plane57 : IntegerPlane := ⟨1574160000000,(-2058052000000),(-367887499047)⟩
theorem rev145_plane57_mem : rev145_plane57 ∈ rev145_planes := by decide
def rev145_plane79 : IntegerPlane := ⟨1440116000000,2129316000000,2741459880216⟩
theorem rev145_plane79_mem : rev145_plane79 ∈ rev145_planes := by decide
def rev145_vertex0 : FractionPoint := fractionRow145[0]!
theorem rev145_vertex0_mem : rev145_vertex0∈fractionRow145 := by decide
def rev145_vertex1 : FractionPoint := fractionRow145[1]!
theorem rev145_vertex1_mem : rev145_vertex1∈fractionRow145 := by decide
def rev145_vertex2 : FractionPoint := fractionRow145[2]!
theorem rev145_vertex2_mem : rev145_vertex2∈fractionRow145 := by decide
def rev145_vertex3 : FractionPoint := fractionRow145[3]!
theorem rev145_vertex3_mem : rev145_vertex3∈fractionRow145 := by decide
def rev145_vertex4 : FractionPoint := fractionRow145[4]!
theorem rev145_vertex4_mem : rev145_vertex4∈fractionRow145 := by decide
def rev145_vertex5 : FractionPoint := fractionRow145[5]!
theorem rev145_vertex5_mem : rev145_vertex5∈fractionRow145 := by decide
def rev145_s0_ll : FractionPoint := ⟨367887499047,483892000000,367887499047,483892000000⟩
theorem rev145_s0_ll_mem : rev145_s0_ll.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane57 rev145_vertex4 rev145_vertex5 rev145_s0_ll
    rev145_vertex4_mem rev145_vertex5_mem (by decide)
def rev145_s0_lr : FractionPoint := ⟨1001990771613779,1306850464000000,128629233867057366153,168097888196008000000⟩
theorem rev145_s0_lr_mem : rev145_s0_lr.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane57 rev145_vertex4 rev145_vertex5 rev145_s0_lr
    rev145_vertex4_mem rev145_vertex5_mem (by decide)
def rev145_s0_ul : FractionPoint := ⟨367887499047,483892000000,367887499047,483892000000⟩
theorem rev145_s0_ul_mem : rev145_s0_ul.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane37 rev145_vertex4 rev145_vertex3 rev145_s0_ul
    rev145_vertex4_mem rev145_vertex3_mem (by decide)
def rev145_s0_ur : FractionPoint := ⟨1001990771613779,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev145_s0_ur_mem : rev145_s0_ur.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane37 rev145_vertex4 rev145_vertex3 rev145_s0_ur
    rev145_vertex4_mem rev145_vertex3_mem (by decide)
theorem rev145_slab0 (p : Point) (hp : p∈IntegerCarrier rev145_planes)
    (hx0 : rev145_s0_ll.real.1≤p.1) (hx1 : p.1≤rev145_s0_lr.real.1) :
    p∈rationalHull (fractionRow145.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev145_plane57 rev145_plane37 rev145_s0_ll rev145_s0_lr rev145_s0_ul rev145_s0_ur
    (by decide) rev145_s0_ll_mem rev145_s0_lr_mem rev145_s0_ul_mem rev145_s0_ur_mem p
    (hp _ rev145_plane57_mem) (hp _ rev145_plane37_mem) hx0 hx1
def rev145_s1_ll : FractionPoint := ⟨1001990771613779,1306850464000000,128629233867057366153,168097888196008000000⟩
theorem rev145_s1_ll_mem : rev145_s1_ll.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane57 rev145_vertex4 rev145_vertex5 rev145_s1_ll
    rev145_vertex4_mem rev145_vertex5_mem (by decide)
def rev145_s1_lr : FractionPoint := ⟨28419630852349427,37052714692000000,2084581308695581675173,2723443342046428000000⟩
theorem rev145_s1_lr_mem : rev145_s1_lr.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane57 rev145_vertex4 rev145_vertex5 rev145_s1_lr
    rev145_vertex4_mem rev145_vertex5_mem (by decide)
def rev145_s1_ul : FractionPoint := ⟨1001990771613779,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev145_s1_ul_mem : rev145_s1_ul.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane36 rev145_vertex3 rev145_vertex2 rev145_s1_ul
    rev145_vertex3_mem rev145_vertex2_mem (by decide)
def rev145_s1_ur : FractionPoint := ⟨28419630852349427,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev145_s1_ur_mem : rev145_s1_ur.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane36 rev145_vertex3 rev145_vertex2 rev145_s1_ur
    rev145_vertex3_mem rev145_vertex2_mem (by decide)
theorem rev145_slab1 (p : Point) (hp : p∈IntegerCarrier rev145_planes)
    (hx0 : rev145_s1_ll.real.1≤p.1) (hx1 : p.1≤rev145_s1_lr.real.1) :
    p∈rationalHull (fractionRow145.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev145_plane57 rev145_plane36 rev145_s1_ll rev145_s1_lr rev145_s1_ul rev145_s1_ur
    (by decide) rev145_s1_ll_mem rev145_s1_lr_mem rev145_s1_ul_mem rev145_s1_ur_mem p
    (hp _ rev145_plane57_mem) (hp _ rev145_plane36_mem) hx0 hx1
def rev145_s2_ll : FractionPoint := ⟨28419630852349427,37052714692000000,2084581308695581675173,2723443342046428000000⟩
theorem rev145_s2_ll_mem : rev145_s2_ll.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane57 rev145_vertex4 rev145_vertex5 rev145_s2_ll
    rev145_vertex4_mem rev145_vertex5_mem (by decide)
def rev145_s2_lr : FractionPoint := ⟨342682485027,446179000000,703580737067393733,918259583308000000⟩
theorem rev145_s2_lr_mem : rev145_s2_lr.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane57 rev145_vertex4 rev145_vertex5 rev145_s2_lr
    rev145_vertex4_mem rev145_vertex5_mem (by decide)
def rev145_s2_ul : FractionPoint := ⟨28419630852349427,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev145_s2_ul_mem : rev145_s2_ul.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane79 rev145_vertex2 rev145_vertex1 rev145_s2_ul
    rev145_vertex2_mem rev145_vertex1_mem (by decide)
def rev145_s2_ur : FractionPoint := ⟨342682485027,446179000000,342682485027,446179000000⟩
theorem rev145_s2_ur_mem : rev145_s2_ur.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane79 rev145_vertex2 rev145_vertex1 rev145_s2_ur
    rev145_vertex2_mem rev145_vertex1_mem (by decide)
theorem rev145_slab2 (p : Point) (hp : p∈IntegerCarrier rev145_planes)
    (hx0 : rev145_s2_ll.real.1≤p.1) (hx1 : p.1≤rev145_s2_lr.real.1) :
    p∈rationalHull (fractionRow145.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev145_plane57 rev145_plane79 rev145_s2_ll rev145_s2_lr rev145_s2_ul rev145_s2_ur
    (by decide) rev145_s2_ll_mem rev145_s2_lr_mem rev145_s2_ul_mem rev145_s2_ur_mem p
    (hp _ rev145_plane57_mem) (hp _ rev145_plane79_mem) hx0 hx1
def rev145_s3_ll : FractionPoint := ⟨342682485027,446179000000,703580737067393733,918259583308000000⟩
theorem rev145_s3_ll_mem : rev145_s3_ll.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane57 rev145_vertex4 rev145_vertex5 rev145_s3_ll
    rev145_vertex4_mem rev145_vertex5_mem (by decide)
def rev145_s3_lr : FractionPoint := ⟨16877002803328811,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev145_s3_lr_mem : rev145_s3_lr.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane57 rev145_vertex4 rev145_vertex5 rev145_s3_lr
    rev145_vertex4_mem rev145_vertex5_mem (by decide)
def rev145_s3_ul : FractionPoint := ⟨342682485027,446179000000,342682485027,446179000000⟩
theorem rev145_s3_ul_mem : rev145_s3_ul.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane19 rev145_vertex1 rev145_vertex0 rev145_s3_ul
    rev145_vertex1_mem rev145_vertex0_mem (by decide)
def rev145_s3_ur : FractionPoint := ⟨16877002803328811,21955087795200000,1443602396189753870029,1882016262813824000000⟩
theorem rev145_s3_ur_mem : rev145_s3_ur.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane19 rev145_vertex1 rev145_vertex0 rev145_s3_ur
    rev145_vertex1_mem rev145_vertex0_mem (by decide)
theorem rev145_slab3 (p : Point) (hp : p∈IntegerCarrier rev145_planes)
    (hx0 : rev145_s3_ll.real.1≤p.1) (hx1 : p.1≤rev145_s3_lr.real.1) :
    p∈rationalHull (fractionRow145.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev145_plane57 rev145_plane19 rev145_s3_ll rev145_s3_lr rev145_s3_ul rev145_s3_ur
    (by decide) rev145_s3_ll_mem rev145_s3_lr_mem rev145_s3_ul_mem rev145_s3_ur_mem p
    (hp _ rev145_plane57_mem) (hp _ rev145_plane19_mem) hx0 hx1
def rev145_s4_ll : FractionPoint := ⟨16877002803328811,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev145_s4_ll_mem : rev145_s4_ll.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane56 rev145_vertex5 rev145_vertex0 rev145_s4_ll
    rev145_vertex5_mem rev145_vertex0_mem (by decide)
def rev145_s4_lr : FractionPoint := ⟨119631870441922553,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev145_s4_lr_mem : rev145_s4_lr.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane56 rev145_vertex5 rev145_vertex0 rev145_s4_lr
    rev145_vertex5_mem rev145_vertex0_mem (by decide)
def rev145_s4_ul : FractionPoint := ⟨16877002803328811,21955087795200000,1443602396189753870029,1882016262813824000000⟩
theorem rev145_s4_ul_mem : rev145_s4_ul.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane19 rev145_vertex1 rev145_vertex0 rev145_s4_ul
    rev145_vertex1_mem rev145_vertex0_mem (by decide)
def rev145_s4_ur : FractionPoint := ⟨119631870441922553,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev145_s4_ur_mem : rev145_s4_ur.real ∈ rationalHull (fractionRow145.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow145 rev145_plane19 rev145_vertex1 rev145_vertex0 rev145_s4_ur
    rev145_vertex1_mem rev145_vertex0_mem (by decide)
theorem rev145_slab4 (p : Point) (hp : p∈IntegerCarrier rev145_planes)
    (hx0 : rev145_s4_ll.real.1≤p.1) (hx1 : p.1≤rev145_s4_lr.real.1) :
    p∈rationalHull (fractionRow145.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev145_plane56 rev145_plane19 rev145_s4_ll rev145_s4_lr rev145_s4_ul rev145_s4_ur
    (by decide) rev145_s4_ll_mem rev145_s4_lr_mem rev145_s4_ul_mem rev145_s4_ur_mem p
    (hp _ rev145_plane56_mem) (hp _ rev145_plane19_mem) hx0 hx1
theorem rev145_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev145_planes) : rev145_s0_ll.real.1≤p.1 := by
  have hc := rev145_plane37.combine_sound rev145_plane57 2058052000000 1574160000000 (by decide) (by decide) p
    (hp _ rev145_plane37_mem) (hp _ rev145_plane57_mem)
  exact (rev145_plane37.combine rev145_plane57 2058052000000 1574160000000).xBoundCheck_sound rev145_s0_ll.nx rev145_s0_ll.dx true (by decide) p hc
theorem rev145_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev145_planes) : p.1≤rev145_s4_lr.real.1 := by
  have hc := rev145_plane19.combine_sound rev145_plane56 202532000000 1440116000000 (by decide) (by decide) p
    (hp _ rev145_plane19_mem) (hp _ rev145_plane56_mem)
  exact (rev145_plane19.combine rev145_plane56 202532000000 1440116000000).xBoundCheck_sound rev145_s4_lr.nx rev145_s4_lr.dx false (by decide) p hc
theorem rev145_hull (p : Point) (hp : p∈IntegerCarrier rev145_planes) :
    p∈rationalHull (fractionRow145.map FractionPoint.rational) := by
  have hxlo := rev145_bound0_lo p hp
  have hxhi := rev145_bound0_hi p hp
  by_cases h0 : p.1≤rev145_s0_lr.real.1
  · exact rev145_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev145_s1_lr.real.1
  · exact rev145_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev145_s2_lr.real.1
  · exact rev145_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev145_s3_lr.real.1
  · exact rev145_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev145_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull145 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,8,8,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow145 := by
  rw [← fractionRow145_correct]
  exact rev145_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull145
