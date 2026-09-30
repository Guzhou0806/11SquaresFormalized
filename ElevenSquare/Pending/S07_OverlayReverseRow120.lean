import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks15
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev120_planes : List IntegerPlane := integerOverlayPlanes ![8,15,0,3]
def rev120_plane0 : IntegerPlane := ⟨(-1),0,0⟩
theorem rev120_plane0_mem : rev120_plane0 ∈ rev120_planes := by decide
def rev120_plane16 : IntegerPlane := ⟨202532000000,1861776000000,1478404260553⟩
theorem rev120_plane16_mem : rev120_plane16 ∈ rev120_planes := by decide
def rev120_plane45 : IntegerPlane := ⟨(-699324000000),(-2145688000000),(-1695048727641)⟩
theorem rev120_plane45_mem : rev120_plane45 ∈ rev120_planes := by decide
def rev120_plane49 : IntegerPlane := ⟨1440116000000,(-2129316000000),(-1301343880216)⟩
theorem rev120_plane49_mem : rev120_plane49 ∈ rev120_planes := by decide
def rev120_plane66 : IntegerPlane := ⟨287616000000,(-1855520000000),(-1356143759600)⟩
theorem rev120_plane66_mem : rev120_plane66 ∈ rev120_planes := by decide
def rev120_plane71 : IntegerPlane := ⟨1861776000000,202532000000,585903739447⟩
theorem rev120_plane71_mem : rev120_plane71 ∈ rev120_planes := by decide
def rev120_vertex0 : FractionPoint := fractionRow120[0]!
theorem rev120_vertex0_mem : rev120_vertex0∈fractionRow120 := by decide
def rev120_vertex1 : FractionPoint := fractionRow120[1]!
theorem rev120_vertex1_mem : rev120_vertex1∈fractionRow120 := by decide
def rev120_vertex2 : FractionPoint := fractionRow120[2]!
theorem rev120_vertex2_mem : rev120_vertex2∈fractionRow120 := by decide
def rev120_vertex3 : FractionPoint := fractionRow120[3]!
theorem rev120_vertex3_mem : rev120_vertex3∈fractionRow120 := by decide
def rev120_vertex4 : FractionPoint := fractionRow120[4]!
theorem rev120_vertex4_mem : rev120_vertex4∈fractionRow120 := by decide
def rev120_vertex5 : FractionPoint := fractionRow120[5]!
theorem rev120_vertex5_mem : rev120_vertex5∈fractionRow120 := by decide
def rev120_s0_ll : FractionPoint := ⟨0,1,1695048727641,2145688000000⟩
theorem rev120_s0_ll_mem : rev120_s0_ll.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane45 rev120_vertex1 rev120_vertex2 rev120_s0_ll
    rev120_vertex1_mem rev120_vertex2_mem (by decide)
def rev120_s0_lr : FractionPoint := ⟨1470846399148897,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev120_s0_lr_mem : rev120_s0_lr.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane45 rev120_vertex1 rev120_vertex2 rev120_s0_lr
    rev120_vertex1_mem rev120_vertex2_mem (by decide)
def rev120_s0_ul : FractionPoint := ⟨0,1,1478404260553,1861776000000⟩
theorem rev120_s0_ul_mem : rev120_s0_ul.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane16 rev120_vertex0 rev120_vertex5 rev120_s0_ul
    rev120_vertex0_mem rev120_vertex5_mem (by decide)
def rev120_s0_ur : FractionPoint := ⟨1470846399148897,11967149176800000,10871494291713763909729,13925094453616248000000⟩
theorem rev120_s0_ur_mem : rev120_s0_ur.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane16 rev120_vertex0 rev120_vertex5 rev120_s0_ur
    rev120_vertex0_mem rev120_vertex5_mem (by decide)
theorem rev120_slab0 (p : Point) (hp : p∈IntegerCarrier rev120_planes)
    (hx0 : rev120_s0_ll.real.1≤p.1) (hx1 : p.1≤rev120_s0_lr.real.1) :
    p∈rationalHull (fractionRow120.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev120_plane45 rev120_plane16 rev120_s0_ll rev120_s0_lr rev120_s0_ul rev120_s0_ur
    (by decide) rev120_s0_ll_mem rev120_s0_lr_mem rev120_s0_ul_mem rev120_s0_ur_mem p
    (hp _ rev120_plane45_mem) (hp _ rev120_plane16_mem) hx0 hx1
def rev120_s1_ll : FractionPoint := ⟨1470846399148897,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev120_s1_ll_mem : rev120_s1_ll.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane66 rev120_vertex2 rev120_vertex3 rev120_s1_ll
    rev120_vertex2_mem rev120_vertex3_mem (by decide)
def rev120_s1_lr : FractionPoint := ⟨1478090653118879,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev120_s1_lr_mem : rev120_s1_lr.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane66 rev120_vertex2 rev120_vertex3 rev120_s1_lr
    rev120_vertex2_mem rev120_vertex3_mem (by decide)
def rev120_s1_ul : FractionPoint := ⟨1470846399148897,11967149176800000,10871494291713763909729,13925094453616248000000⟩
theorem rev120_s1_ul_mem : rev120_s1_ul.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane16 rev120_vertex0 rev120_vertex5 rev120_s1_ul
    rev120_vertex0_mem rev120_vertex5_mem (by decide)
def rev120_s1_ur : FractionPoint := ⟨1478090653118879,6436683405200000,23041648784802498183619,29959156708499088000000⟩
theorem rev120_s1_ur_mem : rev120_s1_ur.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane16 rev120_vertex0 rev120_vertex5 rev120_s1_ur
    rev120_vertex0_mem rev120_vertex5_mem (by decide)
theorem rev120_slab1 (p : Point) (hp : p∈IntegerCarrier rev120_planes)
    (hx0 : rev120_s1_ll.real.1≤p.1) (hx1 : p.1≤rev120_s1_lr.real.1) :
    p∈rationalHull (fractionRow120.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev120_plane66 rev120_plane16 rev120_s1_ll rev120_s1_lr rev120_s1_ul rev120_s1_ur
    (by decide) rev120_s1_ll_mem rev120_s1_lr_mem rev120_s1_ul_mem rev120_s1_ur_mem p
    (hp _ rev120_plane66_mem) (hp _ rev120_plane16_mem) hx0 hx1
def rev120_s2_ll : FractionPoint := ⟨1478090653118879,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev120_s2_ll_mem : rev120_s2_ll.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane49 rev120_vertex3 rev120_vertex4 rev120_s2_ll
    rev120_vertex3_mem rev120_vertex4_mem (by decide)
def rev120_s2_lr : FractionPoint := ⟨383371739447,1659244000000,677836700277643139,883263699276000000⟩
theorem rev120_s2_lr_mem : rev120_s2_lr.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane49 rev120_vertex3 rev120_vertex4 rev120_s2_lr
    rev120_vertex3_mem rev120_vertex4_mem (by decide)
def rev120_s2_ul : FractionPoint := ⟨1478090653118879,6436683405200000,23041648784802498183619,29959156708499088000000⟩
theorem rev120_s2_ul_mem : rev120_s2_ul.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane16 rev120_vertex0 rev120_vertex5 rev120_s2_ul
    rev120_vertex0_mem rev120_vertex5_mem (by decide)
def rev120_s2_ur : FractionPoint := ⟨383371739447,1659244000000,1275872260553,1659244000000⟩
theorem rev120_s2_ur_mem : rev120_s2_ur.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane16 rev120_vertex0 rev120_vertex5 rev120_s2_ur
    rev120_vertex0_mem rev120_vertex5_mem (by decide)
theorem rev120_slab2 (p : Point) (hp : p∈IntegerCarrier rev120_planes)
    (hx0 : rev120_s2_ll.real.1≤p.1) (hx1 : p.1≤rev120_s2_lr.real.1) :
    p∈rationalHull (fractionRow120.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev120_plane49 rev120_plane16 rev120_s2_ll rev120_s2_lr rev120_s2_ul rev120_s2_ur
    (by decide) rev120_s2_ll_mem rev120_s2_lr_mem rev120_s2_ul_mem rev120_s2_ur_mem p
    (hp _ rev120_plane49_mem) (hp _ rev120_plane16_mem) hx0 hx1
def rev120_s3_ll : FractionPoint := ⟨383371739447,1659244000000,677836700277643139,883263699276000000⟩
theorem rev120_s3_ll_mem : rev120_s3_ll.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane49 rev120_vertex3 rev120_vertex4 rev120_s3_ll
    rev120_vertex3_mem rev120_vertex4_mem (by decide)
def rev120_s3_lr : FractionPoint := ⟨49200521405821067,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev120_s3_lr_mem : rev120_s3_lr.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane49 rev120_vertex3 rev120_vertex4 rev120_s3_lr
    rev120_vertex3_mem rev120_vertex4_mem (by decide)
def rev120_s3_ul : FractionPoint := ⟨383371739447,1659244000000,1275872260553,1659244000000⟩
theorem rev120_s3_ul_mem : rev120_s3_ul.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane71 rev120_vertex5 rev120_vertex4 rev120_s3_ul
    rev120_vertex5_mem rev120_vertex4_mem (by decide)
def rev120_s3_ur : FractionPoint := ⟨49200521405821067,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev120_s3_ur_mem : rev120_s3_ur.real ∈ rationalHull (fractionRow120.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow120 rev120_plane71 rev120_vertex5 rev120_vertex4 rev120_s3_ur
    rev120_vertex5_mem rev120_vertex4_mem (by decide)
theorem rev120_slab3 (p : Point) (hp : p∈IntegerCarrier rev120_planes)
    (hx0 : rev120_s3_ll.real.1≤p.1) (hx1 : p.1≤rev120_s3_lr.real.1) :
    p∈rationalHull (fractionRow120.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev120_plane49 rev120_plane71 rev120_s3_ll rev120_s3_lr rev120_s3_ul rev120_s3_ur
    (by decide) rev120_s3_ll_mem rev120_s3_lr_mem rev120_s3_ul_mem rev120_s3_ur_mem p
    (hp _ rev120_plane49_mem) (hp _ rev120_plane71_mem) hx0 hx1
theorem rev120_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev120_planes) : rev120_s0_ll.real.1≤p.1 := by
  have hc := rev120_plane0.combine_sound rev120_plane0 1 0 (by decide) (by decide) p
    (hp _ rev120_plane0_mem) (hp _ rev120_plane0_mem)
  exact (rev120_plane0.combine rev120_plane0 1 0).xBoundCheck_sound rev120_s0_ll.nx rev120_s0_ll.dx true (by decide) p hc
theorem rev120_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev120_planes) : p.1≤rev120_s3_lr.real.1 := by
  have hc := rev120_plane49.combine_sound rev120_plane71 202532000000 2129316000000 (by decide) (by decide) p
    (hp _ rev120_plane49_mem) (hp _ rev120_plane71_mem)
  exact (rev120_plane49.combine rev120_plane71 202532000000 2129316000000).xBoundCheck_sound rev120_s3_lr.nx rev120_s3_lr.dx false (by decide) p hc
theorem rev120_hull (p : Point) (hp : p∈IntegerCarrier rev120_planes) :
    p∈rationalHull (fractionRow120.map FractionPoint.rational) := by
  have hxlo := rev120_bound0_lo p hp
  have hxhi := rev120_bound0_hi p hp
  by_cases h0 : p.1≤rev120_s0_lr.real.1
  · exact rev120_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev120_s1_lr.real.1
  · exact rev120_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev120_s2_lr.real.1
  · exact rev120_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev120_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull120 (p : Point)
    (hp : ∀ g, ClosedCell ((![8,15,0,3] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow120 := by
  rw [← fractionRow120_correct]
  exact rev120_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull120
