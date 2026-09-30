import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks0
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev3_planes : List IntegerPlane := integerOverlayPlanes ![0,3,7,0]
def rev3_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev3_plane2_mem : rev3_plane2 ∈ rev3_planes := by decide
def rev3_plane5 : IntegerPlane := ⟨2145688000000,(-699324000000),450639272359⟩
theorem rev3_plane5_mem : rev3_plane5 ∈ rev3_planes := by decide
def rev3_plane9 : IntegerPlane := ⟨2129316000000,1440116000000,827972119784⟩
theorem rev3_plane9_mem : rev3_plane9 ∈ rev3_planes := by decide
def rev3_plane26 : IntegerPlane := ⟨1855520000000,287616000000,499376240400⟩
theorem rev3_plane26_mem : rev3_plane26 ∈ rev3_planes := by decide
def rev3_plane31 : IntegerPlane := ⟨(-202532000000),1861776000000,383371739447⟩
theorem rev3_plane31_mem : rev3_plane31 ∈ rev3_planes := by decide
def rev3_plane47 : IntegerPlane := ⟨(-1861776000000),202532000000,(-383371739447)⟩
theorem rev3_plane47_mem : rev3_plane47 ∈ rev3_planes := by decide
def rev3_vertex0 : FractionPoint := fractionRow3[0]!
theorem rev3_vertex0_mem : rev3_vertex0∈fractionRow3 := by decide
def rev3_vertex1 : FractionPoint := fractionRow3[1]!
theorem rev3_vertex1_mem : rev3_vertex1∈fractionRow3 := by decide
def rev3_vertex2 : FractionPoint := fractionRow3[2]!
theorem rev3_vertex2_mem : rev3_vertex2∈fractionRow3 := by decide
def rev3_vertex3 : FractionPoint := fractionRow3[3]!
theorem rev3_vertex3_mem : rev3_vertex3∈fractionRow3 := by decide
def rev3_vertex4 : FractionPoint := fractionRow3[4]!
theorem rev3_vertex4_mem : rev3_vertex4∈fractionRow3 := by decide
def rev3_vertex5 : FractionPoint := fractionRow3[5]!
theorem rev3_vertex5_mem : rev3_vertex5∈fractionRow3 := by decide
def rev3_s0_ll : FractionPoint := ⟨383371739447,1861776000000,0,1⟩
theorem rev3_s0_ll_mem : rev3_s0_ll.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane2 rev3_vertex0 rev3_vertex1 rev3_s0_ll
    rev3_vertex0_mem rev3_vertex1_mem (by decide)
def rev3_s0_lr : FractionPoint := ⟨450639272359,2145688000000,0,1⟩
theorem rev3_s0_lr_mem : rev3_s0_lr.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane2 rev3_vertex0 rev3_vertex1 rev3_s0_lr
    rev3_vertex0_mem rev3_vertex1_mem (by decide)
def rev3_s0_ul : FractionPoint := ⟨383371739447,1861776000000,0,1⟩
theorem rev3_s0_ul_mem : rev3_s0_ul.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane47 rev3_vertex0 rev3_vertex5 rev3_s0_ul
    rev3_vertex0_mem rev3_vertex5_mem (by decide)
def rev3_s0_ur : FractionPoint := ⟨450639272359,2145688000000,2049155133111881,54321310252000000⟩
theorem rev3_s0_ur_mem : rev3_s0_ur.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane47 rev3_vertex0 rev3_vertex5 rev3_s0_ur
    rev3_vertex0_mem rev3_vertex5_mem (by decide)
theorem rev3_slab0 (p : Point) (hp : p∈IntegerCarrier rev3_planes)
    (hx0 : rev3_s0_ll.real.1≤p.1) (hx1 : p.1≤rev3_s0_lr.real.1) :
    p∈rationalHull (fractionRow3.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev3_plane2 rev3_plane47 rev3_s0_ll rev3_s0_lr rev3_s0_ul rev3_s0_ur
    (by decide) rev3_s0_ll_mem rev3_s0_lr_mem rev3_s0_ul_mem rev3_s0_ur_mem p
    (hp _ rev3_plane2_mem) (hp _ rev3_plane47_mem) hx0 hx1
def rev3_s1_ll : FractionPoint := ⟨450639272359,2145688000000,0,1⟩
theorem rev3_s1_ll_mem : rev3_s1_ll.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane5 rev3_vertex1 rev3_vertex2 rev3_s1_ll
    rev3_vertex1_mem rev3_vertex2_mem (by decide)
def rev3_s1_lr : FractionPoint := ⟨383371739447,1659244000000,3743781602225897,58017457552800000⟩
theorem rev3_s1_lr_mem : rev3_s1_lr.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane5 rev3_vertex1 rev3_vertex2 rev3_s1_lr
    rev3_vertex1_mem rev3_vertex2_mem (by decide)
def rev3_s1_ul : FractionPoint := ⟨450639272359,2145688000000,2049155133111881,54321310252000000⟩
theorem rev3_s1_ul_mem : rev3_s1_ul.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane47 rev3_vertex0 rev3_vertex5 rev3_s1_ul
    rev3_vertex0_mem rev3_vertex5_mem (by decide)
def rev3_s1_ur : FractionPoint := ⟨383371739447,1659244000000,383371739447,1659244000000⟩
theorem rev3_s1_ur_mem : rev3_s1_ur.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane47 rev3_vertex0 rev3_vertex5 rev3_s1_ur
    rev3_vertex0_mem rev3_vertex5_mem (by decide)
theorem rev3_slab1 (p : Point) (hp : p∈IntegerCarrier rev3_planes)
    (hx0 : rev3_s1_ll.real.1≤p.1) (hx1 : p.1≤rev3_s1_lr.real.1) :
    p∈rationalHull (fractionRow3.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev3_plane5 rev3_plane47 rev3_s1_ll rev3_s1_lr rev3_s1_ul rev3_s1_ur
    (by decide) rev3_s1_ll_mem rev3_s1_lr_mem rev3_s1_ul_mem rev3_s1_ur_mem p
    (hp _ rev3_plane5_mem) (hp _ rev3_plane47_mem) hx0 hx1
def rev3_s2_ll : FractionPoint := ⟨383371739447,1659244000000,3743781602225897,58017457552800000⟩
theorem rev3_s2_ll_mem : rev3_s2_ll.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane5 rev3_vertex1 rev3_vertex2 rev3_s2_ll
    rev3_vertex1_mem rev3_vertex2_mem (by decide)
def rev3_s2_lr : FractionPoint := ⟨247349711339380133,1063994749732000000,12814371902836772139679,186019266090395292000000⟩
theorem rev3_s2_lr_mem : rev3_s2_lr.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane5 rev3_vertex1 rev3_vertex2 rev3_s2_lr
    rev3_vertex1_mem rev3_vertex2_mem (by decide)
def rev3_s2_ul : FractionPoint := ⟨383371739447,1659244000000,383371739447,1659244000000⟩
theorem rev3_s2_ul_mem : rev3_s2_ul.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane31 rev3_vertex5 rev3_vertex4 rev3_s2_ul
    rev3_vertex5_mem rev3_vertex4_mem (by decide)
def rev3_s2_ur : FractionPoint := ⟨247349711339380133,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev3_s2_ur_mem : rev3_s2_ur.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane31 rev3_vertex5 rev3_vertex4 rev3_s2_ur
    rev3_vertex5_mem rev3_vertex4_mem (by decide)
theorem rev3_slab2 (p : Point) (hp : p∈IntegerCarrier rev3_planes)
    (hx0 : rev3_s2_ll.real.1≤p.1) (hx1 : p.1≤rev3_s2_lr.real.1) :
    p∈rationalHull (fractionRow3.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev3_plane5 rev3_plane31 rev3_s2_ll rev3_s2_lr rev3_s2_ul rev3_s2_ur
    (by decide) rev3_s2_ll_mem rev3_s2_lr_mem rev3_s2_ul_mem rev3_s2_ur_mem p
    (hp _ rev3_plane5_mem) (hp _ rev3_plane31_mem) hx0 hx1
def rev3_s3_ll : FractionPoint := ⟨247349711339380133,1063994749732000000,12814371902836772139679,186019266090395292000000⟩
theorem rev3_s3_ll_mem : rev3_s3_ll.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane5 rev3_vertex1 rev3_vertex2 rev3_s3_ll
    rev3_vertex1_mem rev3_vertex2_mem (by decide)
def rev3_s3_lr : FractionPoint := ⟨7515963822126429,32183417026000000,811900875473960701909,11253317964145212000000⟩
theorem rev3_s3_lr_mem : rev3_s3_lr.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane5 rev3_vertex1 rev3_vertex2 rev3_s3_lr
    rev3_vertex1_mem rev3_vertex2_mem (by decide)
def rev3_s3_ul : FractionPoint := ⟨247349711339380133,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev3_s3_ul_mem : rev3_s3_ul.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane9 rev3_vertex4 rev3_vertex3 rev3_s3_ul
    rev3_vertex4_mem rev3_vertex3_mem (by decide)
def rev3_s3_ur : FractionPoint := ⟨7515963822126429,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev3_s3_ur_mem : rev3_s3_ur.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane9 rev3_vertex4 rev3_vertex3 rev3_s3_ur
    rev3_vertex4_mem rev3_vertex3_mem (by decide)
theorem rev3_slab3 (p : Point) (hp : p∈IntegerCarrier rev3_planes)
    (hx0 : rev3_s3_ll.real.1≤p.1) (hx1 : p.1≤rev3_s3_lr.real.1) :
    p∈rationalHull (fractionRow3.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev3_plane5 rev3_plane9 rev3_s3_ll rev3_s3_lr rev3_s3_ul rev3_s3_ur
    (by decide) rev3_s3_ll_mem rev3_s3_lr_mem rev3_s3_ul_mem rev3_s3_ur_mem p
    (hp _ rev3_plane5_mem) (hp _ rev3_plane9_mem) hx0 hx1
def rev3_s4_ll : FractionPoint := ⟨7515963822126429,32183417026000000,811900875473960701909,11253317964145212000000⟩
theorem rev3_s4_ll_mem : rev3_s4_ll.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane5 rev3_vertex1 rev3_vertex2 rev3_s4_ll
    rev3_vertex1_mem rev3_vertex2_mem (by decide)
def rev3_s4_lr : FractionPoint := ⟨2493941952605707,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev3_s4_lr_mem : rev3_s4_lr.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane5 rev3_vertex1 rev3_vertex2 rev3_s4_lr
    rev3_vertex1_mem rev3_vertex2_mem (by decide)
def rev3_s4_ul : FractionPoint := ⟨7515963822126429,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev3_s4_ul_mem : rev3_s4_ul.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane26 rev3_vertex3 rev3_vertex2 rev3_s4_ul
    rev3_vertex3_mem rev3_vertex2_mem (by decide)
def rev3_s4_ur : FractionPoint := ⟨2493941952605707,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev3_s4_ur_mem : rev3_s4_ur.real ∈ rationalHull (fractionRow3.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow3 rev3_plane26 rev3_vertex3 rev3_vertex2 rev3_s4_ur
    rev3_vertex3_mem rev3_vertex2_mem (by decide)
theorem rev3_slab4 (p : Point) (hp : p∈IntegerCarrier rev3_planes)
    (hx0 : rev3_s4_ll.real.1≤p.1) (hx1 : p.1≤rev3_s4_lr.real.1) :
    p∈rationalHull (fractionRow3.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev3_plane5 rev3_plane26 rev3_s4_ll rev3_s4_lr rev3_s4_ul rev3_s4_ur
    (by decide) rev3_s4_ll_mem rev3_s4_lr_mem rev3_s4_ul_mem rev3_s4_ur_mem p
    (hp _ rev3_plane5_mem) (hp _ rev3_plane26_mem) hx0 hx1
theorem rev3_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev3_planes) : rev3_s0_ll.real.1≤p.1 := by
  have hc := rev3_plane2.combine_sound rev3_plane47 202532000000 1 (by decide) (by decide) p
    (hp _ rev3_plane2_mem) (hp _ rev3_plane47_mem)
  exact (rev3_plane2.combine rev3_plane47 202532000000 1).xBoundCheck_sound rev3_s0_ll.nx rev3_s0_ll.dx true (by decide) p hc
theorem rev3_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev3_planes) : p.1≤rev3_s4_lr.real.1 := by
  have hc := rev3_plane5.combine_sound rev3_plane26 287616000000 699324000000 (by decide) (by decide) p
    (hp _ rev3_plane5_mem) (hp _ rev3_plane26_mem)
  exact (rev3_plane5.combine rev3_plane26 287616000000 699324000000).xBoundCheck_sound rev3_s4_lr.nx rev3_s4_lr.dx false (by decide) p hc
theorem rev3_hull (p : Point) (hp : p∈IntegerCarrier rev3_planes) :
    p∈rationalHull (fractionRow3.map FractionPoint.rational) := by
  have hxlo := rev3_bound0_lo p hp
  have hxhi := rev3_bound0_hi p hp
  by_cases h0 : p.1≤rev3_s0_lr.real.1
  · exact rev3_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev3_s1_lr.real.1
  · exact rev3_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev3_s2_lr.real.1
  · exact rev3_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev3_s3_lr.real.1
  · exact rev3_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev3_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull3 (p : Point)
    (hp : ∀ g, ClosedCell ((![0,3,7,0] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow3 := by
  rw [← fractionRow3_correct]
  exact rev3_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull3
