import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks4
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev34_planes : List IntegerPlane := integerOverlayPlanes ![3,0,15,8]
def rev34_plane2 : IntegerPlane := ⟨0,(-1),0⟩
theorem rev34_plane2_mem : rev34_plane2 ∈ rev34_planes := by decide
def rev34_plane6 : IntegerPlane := ⟨(-1855520000000),287616000000,(-1356143759600)⟩
theorem rev34_plane6_mem : rev34_plane6 ∈ rev34_planes := by decide
def rev34_plane11 : IntegerPlane := ⟨202532000000,1861776000000,585903739447⟩
theorem rev34_plane11_mem : rev34_plane11 ∈ rev34_planes := by decide
def rev34_plane25 : IntegerPlane := ⟨(-2145688000000),(-699324000000),(-1695048727641)⟩
theorem rev34_plane25_mem : rev34_plane25 ∈ rev34_planes := by decide
def rev34_plane29 : IntegerPlane := ⟨(-2129316000000),1440116000000,(-1301343880216)⟩
theorem rev34_plane29_mem : rev34_plane29 ∈ rev34_planes := by decide
def rev34_plane76 : IntegerPlane := ⟨1861776000000,202532000000,1478404260553⟩
theorem rev34_plane76_mem : rev34_plane76 ∈ rev34_planes := by decide
def rev34_vertex0 : FractionPoint := fractionRow34[0]!
theorem rev34_vertex0_mem : rev34_vertex0∈fractionRow34 := by decide
def rev34_vertex1 : FractionPoint := fractionRow34[1]!
theorem rev34_vertex1_mem : rev34_vertex1∈fractionRow34 := by decide
def rev34_vertex2 : FractionPoint := fractionRow34[2]!
theorem rev34_vertex2_mem : rev34_vertex2∈fractionRow34 := by decide
def rev34_vertex3 : FractionPoint := fractionRow34[3]!
theorem rev34_vertex3_mem : rev34_vertex3∈fractionRow34 := by decide
def rev34_vertex4 : FractionPoint := fractionRow34[4]!
theorem rev34_vertex4_mem : rev34_vertex4∈fractionRow34 := by decide
def rev34_vertex5 : FractionPoint := fractionRow34[5]!
theorem rev34_vertex5_mem : rev34_vertex5∈fractionRow34 := by decide
def rev34_s0_ll : FractionPoint := ⟨7478682361394293,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev34_s0_ll_mem : rev34_s0_ll.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane25 rev34_vertex5 rev34_vertex0 rev34_s0_ll
    rev34_vertex5_mem rev34_vertex0_mem (by decide)
def rev34_s0_lr : FractionPoint := ⟨24667453203873571,32183417026000000,811900875473960701909,11253317964145212000000⟩
theorem rev34_s0_lr_mem : rev34_s0_lr.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane25 rev34_vertex5 rev34_vertex0 rev34_s0_lr
    rev34_vertex5_mem rev34_vertex0_mem (by decide)
def rev34_s0_ul : FractionPoint := ⟨7478682361394293,9972624314000000,1470846399148897,11967149176800000⟩
theorem rev34_s0_ul_mem : rev34_s0_ul.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane6 rev34_vertex5 rev34_vertex4 rev34_s0_ul
    rev34_vertex5_mem rev34_vertex4_mem (by decide)
def rev34_s0_ur : FractionPoint := ⟨24667453203873571,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev34_s0_ur_mem : rev34_s0_ur.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane6 rev34_vertex5 rev34_vertex4 rev34_s0_ur
    rev34_vertex5_mem rev34_vertex4_mem (by decide)
theorem rev34_slab0 (p : Point) (hp : p∈IntegerCarrier rev34_planes)
    (hx0 : rev34_s0_ll.real.1≤p.1) (hx1 : p.1≤rev34_s0_lr.real.1) :
    p∈rationalHull (fractionRow34.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev34_plane25 rev34_plane6 rev34_s0_ll rev34_s0_lr rev34_s0_ul rev34_s0_ur
    (by decide) rev34_s0_ll_mem rev34_s0_lr_mem rev34_s0_ul_mem rev34_s0_ur_mem p
    (hp _ rev34_plane25_mem) (hp _ rev34_plane6_mem) hx0 hx1
def rev34_s1_ll : FractionPoint := ⟨24667453203873571,32183417026000000,811900875473960701909,11253317964145212000000⟩
theorem rev34_s1_ll_mem : rev34_s1_ll.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane25 rev34_vertex5 rev34_vertex0 rev34_s1_ll
    rev34_vertex5_mem rev34_vertex0_mem (by decide)
def rev34_s1_lr : FractionPoint := ⟨816645038392619867,1063994749732000000,12814371902836772139679,186019266090395292000000⟩
theorem rev34_s1_lr_mem : rev34_s1_lr.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane25 rev34_vertex5 rev34_vertex0 rev34_s1_lr
    rev34_vertex5_mem rev34_vertex0_mem (by decide)
def rev34_s1_ul : FractionPoint := ⟨24667453203873571,32183417026000000,1478090653118879,6436683405200000⟩
theorem rev34_s1_ul_mem : rev34_s1_ul.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane29 rev34_vertex4 rev34_vertex3 rev34_s1_ul
    rev34_vertex4_mem rev34_vertex3_mem (by decide)
def rev34_s1_ur : FractionPoint := ⟨816645038392619867,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev34_s1_ur_mem : rev34_s1_ur.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane29 rev34_vertex4 rev34_vertex3 rev34_s1_ur
    rev34_vertex4_mem rev34_vertex3_mem (by decide)
theorem rev34_slab1 (p : Point) (hp : p∈IntegerCarrier rev34_planes)
    (hx0 : rev34_s1_ll.real.1≤p.1) (hx1 : p.1≤rev34_s1_lr.real.1) :
    p∈rationalHull (fractionRow34.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev34_plane25 rev34_plane29 rev34_s1_ll rev34_s1_lr rev34_s1_ul rev34_s1_ur
    (by decide) rev34_s1_ll_mem rev34_s1_lr_mem rev34_s1_ul_mem rev34_s1_ur_mem p
    (hp _ rev34_plane25_mem) (hp _ rev34_plane29_mem) hx0 hx1
def rev34_s2_ll : FractionPoint := ⟨816645038392619867,1063994749732000000,12814371902836772139679,186019266090395292000000⟩
theorem rev34_s2_ll_mem : rev34_s2_ll.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane25 rev34_vertex5 rev34_vertex0 rev34_s2_ll
    rev34_vertex5_mem rev34_vertex0_mem (by decide)
def rev34_s2_lr : FractionPoint := ⟨1275872260553,1659244000000,3743781602225897,58017457552800000⟩
theorem rev34_s2_lr_mem : rev34_s2_lr.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane25 rev34_vertex5 rev34_vertex0 rev34_s2_lr
    rev34_vertex5_mem rev34_vertex0_mem (by decide)
def rev34_s2_ul : FractionPoint := ⟨816645038392619867,1063994749732000000,49200521405821067,212798949946400000⟩
theorem rev34_s2_ul_mem : rev34_s2_ul.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane11 rev34_vertex3 rev34_vertex2 rev34_s2_ul
    rev34_vertex3_mem rev34_vertex2_mem (by decide)
def rev34_s2_ur : FractionPoint := ⟨1275872260553,1659244000000,383371739447,1659244000000⟩
theorem rev34_s2_ur_mem : rev34_s2_ur.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane11 rev34_vertex3 rev34_vertex2 rev34_s2_ur
    rev34_vertex3_mem rev34_vertex2_mem (by decide)
theorem rev34_slab2 (p : Point) (hp : p∈IntegerCarrier rev34_planes)
    (hx0 : rev34_s2_ll.real.1≤p.1) (hx1 : p.1≤rev34_s2_lr.real.1) :
    p∈rationalHull (fractionRow34.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev34_plane25 rev34_plane11 rev34_s2_ll rev34_s2_lr rev34_s2_ul rev34_s2_ur
    (by decide) rev34_s2_ll_mem rev34_s2_lr_mem rev34_s2_ul_mem rev34_s2_ur_mem p
    (hp _ rev34_plane25_mem) (hp _ rev34_plane11_mem) hx0 hx1
def rev34_s3_ll : FractionPoint := ⟨1275872260553,1659244000000,3743781602225897,58017457552800000⟩
theorem rev34_s3_ll_mem : rev34_s3_ll.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane25 rev34_vertex5 rev34_vertex0 rev34_s3_ll
    rev34_vertex5_mem rev34_vertex0_mem (by decide)
def rev34_s3_lr : FractionPoint := ⟨1695048727641,2145688000000,0,1⟩
theorem rev34_s3_lr_mem : rev34_s3_lr.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane25 rev34_vertex5 rev34_vertex0 rev34_s3_lr
    rev34_vertex5_mem rev34_vertex0_mem (by decide)
def rev34_s3_ul : FractionPoint := ⟨1275872260553,1659244000000,383371739447,1659244000000⟩
theorem rev34_s3_ul_mem : rev34_s3_ul.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane76 rev34_vertex2 rev34_vertex1 rev34_s3_ul
    rev34_vertex2_mem rev34_vertex1_mem (by decide)
def rev34_s3_ur : FractionPoint := ⟨1695048727641,2145688000000,2049155133111881,54321310252000000⟩
theorem rev34_s3_ur_mem : rev34_s3_ur.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane76 rev34_vertex2 rev34_vertex1 rev34_s3_ur
    rev34_vertex2_mem rev34_vertex1_mem (by decide)
theorem rev34_slab3 (p : Point) (hp : p∈IntegerCarrier rev34_planes)
    (hx0 : rev34_s3_ll.real.1≤p.1) (hx1 : p.1≤rev34_s3_lr.real.1) :
    p∈rationalHull (fractionRow34.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev34_plane25 rev34_plane76 rev34_s3_ll rev34_s3_lr rev34_s3_ul rev34_s3_ur
    (by decide) rev34_s3_ll_mem rev34_s3_lr_mem rev34_s3_ul_mem rev34_s3_ur_mem p
    (hp _ rev34_plane25_mem) (hp _ rev34_plane76_mem) hx0 hx1
def rev34_s4_ll : FractionPoint := ⟨1695048727641,2145688000000,0,1⟩
theorem rev34_s4_ll_mem : rev34_s4_ll.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane2 rev34_vertex0 rev34_vertex1 rev34_s4_ll
    rev34_vertex0_mem rev34_vertex1_mem (by decide)
def rev34_s4_lr : FractionPoint := ⟨1478404260553,1861776000000,0,1⟩
theorem rev34_s4_lr_mem : rev34_s4_lr.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane2 rev34_vertex0 rev34_vertex1 rev34_s4_lr
    rev34_vertex0_mem rev34_vertex1_mem (by decide)
def rev34_s4_ul : FractionPoint := ⟨1695048727641,2145688000000,2049155133111881,54321310252000000⟩
theorem rev34_s4_ul_mem : rev34_s4_ul.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane76 rev34_vertex2 rev34_vertex1 rev34_s4_ul
    rev34_vertex2_mem rev34_vertex1_mem (by decide)
def rev34_s4_ur : FractionPoint := ⟨1478404260553,1861776000000,0,1⟩
theorem rev34_s4_ur_mem : rev34_s4_ur.real ∈ rationalHull (fractionRow34.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow34 rev34_plane76 rev34_vertex2 rev34_vertex1 rev34_s4_ur
    rev34_vertex2_mem rev34_vertex1_mem (by decide)
theorem rev34_slab4 (p : Point) (hp : p∈IntegerCarrier rev34_planes)
    (hx0 : rev34_s4_ll.real.1≤p.1) (hx1 : p.1≤rev34_s4_lr.real.1) :
    p∈rationalHull (fractionRow34.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev34_plane2 rev34_plane76 rev34_s4_ll rev34_s4_lr rev34_s4_ul rev34_s4_ur
    (by decide) rev34_s4_ll_mem rev34_s4_lr_mem rev34_s4_ul_mem rev34_s4_ur_mem p
    (hp _ rev34_plane2_mem) (hp _ rev34_plane76_mem) hx0 hx1
theorem rev34_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev34_planes) : rev34_s0_ll.real.1≤p.1 := by
  have hc := rev34_plane6.combine_sound rev34_plane25 699324000000 287616000000 (by decide) (by decide) p
    (hp _ rev34_plane6_mem) (hp _ rev34_plane25_mem)
  exact (rev34_plane6.combine rev34_plane25 699324000000 287616000000).xBoundCheck_sound rev34_s0_ll.nx rev34_s0_ll.dx true (by decide) p hc
theorem rev34_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev34_planes) : p.1≤rev34_s4_lr.real.1 := by
  have hc := rev34_plane2.combine_sound rev34_plane76 202532000000 1 (by decide) (by decide) p
    (hp _ rev34_plane2_mem) (hp _ rev34_plane76_mem)
  exact (rev34_plane2.combine rev34_plane76 202532000000 1).xBoundCheck_sound rev34_s4_lr.nx rev34_s4_lr.dx false (by decide) p hc
theorem rev34_hull (p : Point) (hp : p∈IntegerCarrier rev34_planes) :
    p∈rationalHull (fractionRow34.map FractionPoint.rational) := by
  have hxlo := rev34_bound0_lo p hp
  have hxhi := rev34_bound0_hi p hp
  by_cases h0 : p.1≤rev34_s0_lr.real.1
  · exact rev34_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev34_s1_lr.real.1
  · exact rev34_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev34_s2_lr.real.1
  · exact rev34_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev34_s3_lr.real.1
  · exact rev34_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev34_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull34 (p : Point)
    (hp : ∀ g, ClosedCell ((![3,0,15,8] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow34 := by
  rw [← fractionRow34_correct]
  exact rev34_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull34
