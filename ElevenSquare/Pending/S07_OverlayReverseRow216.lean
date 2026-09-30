import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks27
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev216_planes : List IntegerPlane := integerOverlayPlanes ![15,12,8,15]
def rev216_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev216_plane3_mem : rev216_plane3 ∈ rev216_planes := by decide
def rev216_plane14 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-2741459880216)⟩
theorem rev216_plane14_mem : rev216_plane14 ∈ rev216_planes := by decide
def rev216_plane18 : IntegerPlane := ⟨(-2145688000000),699324000000,(-995724727641)⟩
theorem rev216_plane18_mem : rev216_plane18 ∈ rev216_planes := by decide
def rev216_plane32 : IntegerPlane := ⟨202532000000,(-1861776000000),(-1275872260553)⟩
theorem rev216_plane32_mem : rev216_plane32 ∈ rev216_planes := by decide
def rev216_plane37 : IntegerPlane := ⟨(-1855520000000),(-287616000000),(-1643759759600)⟩
theorem rev216_plane37_mem : rev216_plane37 ∈ rev216_planes := by decide
def rev216_plane56 : IntegerPlane := ⟨1861776000000,(-202532000000),1275872260553⟩
theorem rev216_plane56_mem : rev216_plane56 ∈ rev216_planes := by decide
def rev216_vertex0 : FractionPoint := fractionRow216[0]!
theorem rev216_vertex0_mem : rev216_vertex0∈fractionRow216 := by decide
def rev216_vertex1 : FractionPoint := fractionRow216[1]!
theorem rev216_vertex1_mem : rev216_vertex1∈fractionRow216 := by decide
def rev216_vertex2 : FractionPoint := fractionRow216[2]!
theorem rev216_vertex2_mem : rev216_vertex2∈fractionRow216 := by decide
def rev216_vertex3 : FractionPoint := fractionRow216[3]!
theorem rev216_vertex3_mem : rev216_vertex3∈fractionRow216 := by decide
def rev216_vertex4 : FractionPoint := fractionRow216[4]!
theorem rev216_vertex4_mem : rev216_vertex4∈fractionRow216 := by decide
def rev216_vertex5 : FractionPoint := fractionRow216[5]!
theorem rev216_vertex5_mem : rev216_vertex5∈fractionRow216 := by decide
def rev216_s0_ll : FractionPoint := ⟨7478682361394293,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev216_s0_ll_mem : rev216_s0_ll.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane37 rev216_vertex2 rev216_vertex3 rev216_s0_ll
    rev216_vertex2_mem rev216_vertex3_mem (by decide)
def rev216_s0_lr : FractionPoint := ⟨24667453203873571,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev216_s0_lr_mem : rev216_s0_lr.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane37 rev216_vertex2 rev216_vertex3 rev216_s0_lr
    rev216_vertex2_mem rev216_vertex3_mem (by decide)
def rev216_s0_ul : FractionPoint := ⟨7478682361394293,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev216_s0_ul_mem : rev216_s0_ul.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane18 rev216_vertex2 rev216_vertex1 rev216_s0_ul
    rev216_vertex2_mem rev216_vertex1_mem (by decide)
def rev216_s0_ur : FractionPoint := ⟨24667453203873571,32183417026000000,10441417088671251298091,11253317964145212000000⟩
theorem rev216_s0_ur_mem : rev216_s0_ur.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane18 rev216_vertex2 rev216_vertex1 rev216_s0_ur
    rev216_vertex2_mem rev216_vertex1_mem (by decide)
theorem rev216_slab0 (p : Point) (hp : p∈IntegerCarrier rev216_planes)
    (hx0 : rev216_s0_ll.real.1≤p.1) (hx1 : p.1≤rev216_s0_lr.real.1) :
    p∈rationalHull (fractionRow216.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev216_plane37 rev216_plane18 rev216_s0_ll rev216_s0_lr rev216_s0_ul rev216_s0_ur
    (by decide) rev216_s0_ll_mem rev216_s0_lr_mem rev216_s0_ul_mem rev216_s0_ur_mem p
    (hp _ rev216_plane37_mem) (hp _ rev216_plane18_mem) hx0 hx1
def rev216_s1_ll : FractionPoint := ⟨24667453203873571,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev216_s1_ll_mem : rev216_s1_ll.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane14 rev216_vertex3 rev216_vertex4 rev216_s1_ll
    rev216_vertex3_mem rev216_vertex4_mem (by decide)
def rev216_s1_lr : FractionPoint := ⟨816645038392619867,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev216_s1_lr_mem : rev216_s1_lr.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane14 rev216_vertex3 rev216_vertex4 rev216_s1_lr
    rev216_vertex3_mem rev216_vertex4_mem (by decide)
def rev216_s1_ul : FractionPoint := ⟨24667453203873571,32183417026000000,10441417088671251298091,11253317964145212000000⟩
theorem rev216_s1_ul_mem : rev216_s1_ul.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane18 rev216_vertex2 rev216_vertex1 rev216_s1_ul
    rev216_vertex2_mem rev216_vertex1_mem (by decide)
def rev216_s1_ur : FractionPoint := ⟨816645038392619867,1063994749732000000,173204894187558519860321,186019266090395292000000⟩
theorem rev216_s1_ur_mem : rev216_s1_ur.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane18 rev216_vertex2 rev216_vertex1 rev216_s1_ur
    rev216_vertex2_mem rev216_vertex1_mem (by decide)
theorem rev216_slab1 (p : Point) (hp : p∈IntegerCarrier rev216_planes)
    (hx0 : rev216_s1_ll.real.1≤p.1) (hx1 : p.1≤rev216_s1_lr.real.1) :
    p∈rationalHull (fractionRow216.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev216_plane14 rev216_plane18 rev216_s1_ll rev216_s1_lr rev216_s1_ul rev216_s1_ur
    (by decide) rev216_s1_ll_mem rev216_s1_lr_mem rev216_s1_ul_mem rev216_s1_ur_mem p
    (hp _ rev216_plane14_mem) (hp _ rev216_plane18_mem) hx0 hx1
def rev216_s2_ll : FractionPoint := ⟨816645038392619867,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev216_s2_ll_mem : rev216_s2_ll.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane32 rev216_vertex4 rev216_vertex5 rev216_s2_ll
    rev216_vertex4_mem rev216_vertex5_mem (by decide)
def rev216_s2_lr : FractionPoint := ⟨1275872260553,1659244000000,1275872260553,1659244000000⟩
theorem rev216_s2_lr_mem : rev216_s2_lr.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane32 rev216_vertex4 rev216_vertex5 rev216_s2_lr
    rev216_vertex4_mem rev216_vertex5_mem (by decide)
def rev216_s2_ul : FractionPoint := ⟨816645038392619867,1063994749732000000,173204894187558519860321,186019266090395292000000⟩
theorem rev216_s2_ul_mem : rev216_s2_ul.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane18 rev216_vertex2 rev216_vertex1 rev216_s2_ul
    rev216_vertex2_mem rev216_vertex1_mem (by decide)
def rev216_s2_ur : FractionPoint := ⟨1275872260553,1659244000000,54273675950574103,58017457552800000⟩
theorem rev216_s2_ur_mem : rev216_s2_ur.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane18 rev216_vertex2 rev216_vertex1 rev216_s2_ur
    rev216_vertex2_mem rev216_vertex1_mem (by decide)
theorem rev216_slab2 (p : Point) (hp : p∈IntegerCarrier rev216_planes)
    (hx0 : rev216_s2_ll.real.1≤p.1) (hx1 : p.1≤rev216_s2_lr.real.1) :
    p∈rationalHull (fractionRow216.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev216_plane32 rev216_plane18 rev216_s2_ll rev216_s2_lr rev216_s2_ul rev216_s2_ur
    (by decide) rev216_s2_ll_mem rev216_s2_lr_mem rev216_s2_ul_mem rev216_s2_ur_mem p
    (hp _ rev216_plane32_mem) (hp _ rev216_plane18_mem) hx0 hx1
def rev216_s3_ll : FractionPoint := ⟨1275872260553,1659244000000,1275872260553,1659244000000⟩
theorem rev216_s3_ll_mem : rev216_s3_ll.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane56 rev216_vertex5 rev216_vertex0 rev216_s3_ll
    rev216_vertex5_mem rev216_vertex0_mem (by decide)
def rev216_s3_lr : FractionPoint := ⟨1695048727641,2145688000000,52272155118888119,54321310252000000⟩
theorem rev216_s3_lr_mem : rev216_s3_lr.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane56 rev216_vertex5 rev216_vertex0 rev216_s3_lr
    rev216_vertex5_mem rev216_vertex0_mem (by decide)
def rev216_s3_ul : FractionPoint := ⟨1275872260553,1659244000000,54273675950574103,58017457552800000⟩
theorem rev216_s3_ul_mem : rev216_s3_ul.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane18 rev216_vertex2 rev216_vertex1 rev216_s3_ul
    rev216_vertex2_mem rev216_vertex1_mem (by decide)
def rev216_s3_ur : FractionPoint := ⟨1695048727641,2145688000000,1,1⟩
theorem rev216_s3_ur_mem : rev216_s3_ur.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane18 rev216_vertex2 rev216_vertex1 rev216_s3_ur
    rev216_vertex2_mem rev216_vertex1_mem (by decide)
theorem rev216_slab3 (p : Point) (hp : p∈IntegerCarrier rev216_planes)
    (hx0 : rev216_s3_ll.real.1≤p.1) (hx1 : p.1≤rev216_s3_lr.real.1) :
    p∈rationalHull (fractionRow216.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev216_plane56 rev216_plane18 rev216_s3_ll rev216_s3_lr rev216_s3_ul rev216_s3_ur
    (by decide) rev216_s3_ll_mem rev216_s3_lr_mem rev216_s3_ul_mem rev216_s3_ur_mem p
    (hp _ rev216_plane56_mem) (hp _ rev216_plane18_mem) hx0 hx1
def rev216_s4_ll : FractionPoint := ⟨1695048727641,2145688000000,52272155118888119,54321310252000000⟩
theorem rev216_s4_ll_mem : rev216_s4_ll.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane56 rev216_vertex5 rev216_vertex0 rev216_s4_ll
    rev216_vertex5_mem rev216_vertex0_mem (by decide)
def rev216_s4_lr : FractionPoint := ⟨1478404260553,1861776000000,1,1⟩
theorem rev216_s4_lr_mem : rev216_s4_lr.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane56 rev216_vertex5 rev216_vertex0 rev216_s4_lr
    rev216_vertex5_mem rev216_vertex0_mem (by decide)
def rev216_s4_ul : FractionPoint := ⟨1695048727641,2145688000000,1,1⟩
theorem rev216_s4_ul_mem : rev216_s4_ul.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane3 rev216_vertex1 rev216_vertex0 rev216_s4_ul
    rev216_vertex1_mem rev216_vertex0_mem (by decide)
def rev216_s4_ur : FractionPoint := ⟨1478404260553,1861776000000,1,1⟩
theorem rev216_s4_ur_mem : rev216_s4_ur.real ∈ rationalHull (fractionRow216.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow216 rev216_plane3 rev216_vertex1 rev216_vertex0 rev216_s4_ur
    rev216_vertex1_mem rev216_vertex0_mem (by decide)
theorem rev216_slab4 (p : Point) (hp : p∈IntegerCarrier rev216_planes)
    (hx0 : rev216_s4_ll.real.1≤p.1) (hx1 : p.1≤rev216_s4_lr.real.1) :
    p∈rationalHull (fractionRow216.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev216_plane56 rev216_plane3 rev216_s4_ll rev216_s4_lr rev216_s4_ul rev216_s4_ur
    (by decide) rev216_s4_ll_mem rev216_s4_lr_mem rev216_s4_ul_mem rev216_s4_ur_mem p
    (hp _ rev216_plane56_mem) (hp _ rev216_plane3_mem) hx0 hx1
theorem rev216_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev216_planes) : rev216_s0_ll.real.1≤p.1 := by
  have hc := rev216_plane18.combine_sound rev216_plane37 287616000000 699324000000 (by decide) (by decide) p
    (hp _ rev216_plane18_mem) (hp _ rev216_plane37_mem)
  exact (rev216_plane18.combine rev216_plane37 287616000000 699324000000).xBoundCheck_sound rev216_s0_ll.nx rev216_s0_ll.dx true (by decide) p hc
theorem rev216_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev216_planes) : p.1≤rev216_s4_lr.real.1 := by
  have hc := rev216_plane3.combine_sound rev216_plane56 202532000000 1 (by decide) (by decide) p
    (hp _ rev216_plane3_mem) (hp _ rev216_plane56_mem)
  exact (rev216_plane3.combine rev216_plane56 202532000000 1).xBoundCheck_sound rev216_s4_lr.nx rev216_s4_lr.dx false (by decide) p hc
theorem rev216_hull (p : Point) (hp : p∈IntegerCarrier rev216_planes) :
    p∈rationalHull (fractionRow216.map FractionPoint.rational) := by
  have hxlo := rev216_bound0_lo p hp
  have hxhi := rev216_bound0_hi p hp
  by_cases h0 : p.1≤rev216_s0_lr.real.1
  · exact rev216_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev216_s1_lr.real.1
  · exact rev216_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev216_s2_lr.real.1
  · exact rev216_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev216_s3_lr.real.1
  · exact rev216_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev216_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull216 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,12,8,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow216 := by
  rw [← fractionRow216_correct]
  exact rev216_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull216
