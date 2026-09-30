import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks23
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev185_planes : List IntegerPlane := integerOverlayPlanes ![12,15,0,7]
def rev185_plane3 : IntegerPlane := ⟨0,1,1⟩
theorem rev185_plane3_mem : rev185_plane3 ∈ rev185_planes := by decide
def rev185_plane12 : IntegerPlane := ⟨(-202532000000),(-1861776000000),(-1478404260553)⟩
theorem rev185_plane12_mem : rev185_plane12 ∈ rev185_planes := by decide
def rev185_plane17 : IntegerPlane := ⟨1855520000000,(-287616000000),211760240400⟩
theorem rev185_plane17_mem : rev185_plane17 ∈ rev185_planes := by decide
def rev185_plane34 : IntegerPlane := ⟨2129316000000,(-1440116000000),(-612143880216)⟩
theorem rev185_plane34_mem : rev185_plane34 ∈ rev185_planes := by decide
def rev185_plane38 : IntegerPlane := ⟨2145688000000,699324000000,1149963272359⟩
theorem rev185_plane38_mem : rev185_plane38 ∈ rev185_planes := by decide
def rev185_plane67 : IntegerPlane := ⟨(-1861776000000),(-202532000000),(-585903739447)⟩
theorem rev185_plane67_mem : rev185_plane67 ∈ rev185_planes := by decide
def rev185_vertex0 : FractionPoint := fractionRow185[0]!
theorem rev185_vertex0_mem : rev185_vertex0∈fractionRow185 := by decide
def rev185_vertex1 : FractionPoint := fractionRow185[1]!
theorem rev185_vertex1_mem : rev185_vertex1∈fractionRow185 := by decide
def rev185_vertex2 : FractionPoint := fractionRow185[2]!
theorem rev185_vertex2_mem : rev185_vertex2∈fractionRow185 := by decide
def rev185_vertex3 : FractionPoint := fractionRow185[3]!
theorem rev185_vertex3_mem : rev185_vertex3∈fractionRow185 := by decide
def rev185_vertex4 : FractionPoint := fractionRow185[4]!
theorem rev185_vertex4_mem : rev185_vertex4∈fractionRow185 := by decide
def rev185_vertex5 : FractionPoint := fractionRow185[5]!
theorem rev185_vertex5_mem : rev185_vertex5∈fractionRow185 := by decide
def rev185_s0_ll : FractionPoint := ⟨383371739447,1861776000000,1,1⟩
theorem rev185_s0_ll_mem : rev185_s0_ll.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane67 rev185_vertex1 rev185_vertex2 rev185_s0_ll
    rev185_vertex1_mem rev185_vertex2_mem (by decide)
def rev185_s0_lr : FractionPoint := ⟨450639272359,2145688000000,52272155118888119,54321310252000000⟩
theorem rev185_s0_lr_mem : rev185_s0_lr.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane67 rev185_vertex1 rev185_vertex2 rev185_s0_lr
    rev185_vertex1_mem rev185_vertex2_mem (by decide)
def rev185_s0_ul : FractionPoint := ⟨383371739447,1861776000000,1,1⟩
theorem rev185_s0_ul_mem : rev185_s0_ul.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane3 rev185_vertex1 rev185_vertex0 rev185_s0_ul
    rev185_vertex1_mem rev185_vertex0_mem (by decide)
def rev185_s0_ur : FractionPoint := ⟨450639272359,2145688000000,1,1⟩
theorem rev185_s0_ur_mem : rev185_s0_ur.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane3 rev185_vertex1 rev185_vertex0 rev185_s0_ur
    rev185_vertex1_mem rev185_vertex0_mem (by decide)
theorem rev185_slab0 (p : Point) (hp : p∈IntegerCarrier rev185_planes)
    (hx0 : rev185_s0_ll.real.1≤p.1) (hx1 : p.1≤rev185_s0_lr.real.1) :
    p∈rationalHull (fractionRow185.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev185_plane67 rev185_plane3 rev185_s0_ll rev185_s0_lr rev185_s0_ul rev185_s0_ur
    (by decide) rev185_s0_ll_mem rev185_s0_lr_mem rev185_s0_ul_mem rev185_s0_ur_mem p
    (hp _ rev185_plane67_mem) (hp _ rev185_plane3_mem) hx0 hx1
def rev185_s1_ll : FractionPoint := ⟨450639272359,2145688000000,52272155118888119,54321310252000000⟩
theorem rev185_s1_ll_mem : rev185_s1_ll.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane67 rev185_vertex1 rev185_vertex2 rev185_s1_ll
    rev185_vertex1_mem rev185_vertex2_mem (by decide)
def rev185_s1_lr : FractionPoint := ⟨383371739447,1659244000000,1275872260553,1659244000000⟩
theorem rev185_s1_lr_mem : rev185_s1_lr.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane67 rev185_vertex1 rev185_vertex2 rev185_s1_lr
    rev185_vertex1_mem rev185_vertex2_mem (by decide)
def rev185_s1_ul : FractionPoint := ⟨450639272359,2145688000000,1,1⟩
theorem rev185_s1_ul_mem : rev185_s1_ul.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane38 rev185_vertex0 rev185_vertex5 rev185_s1_ul
    rev185_vertex0_mem rev185_vertex5_mem (by decide)
def rev185_s1_ur : FractionPoint := ⟨383371739447,1659244000000,54273675950574103,58017457552800000⟩
theorem rev185_s1_ur_mem : rev185_s1_ur.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane38 rev185_vertex0 rev185_vertex5 rev185_s1_ur
    rev185_vertex0_mem rev185_vertex5_mem (by decide)
theorem rev185_slab1 (p : Point) (hp : p∈IntegerCarrier rev185_planes)
    (hx0 : rev185_s1_ll.real.1≤p.1) (hx1 : p.1≤rev185_s1_lr.real.1) :
    p∈rationalHull (fractionRow185.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev185_plane67 rev185_plane38 rev185_s1_ll rev185_s1_lr rev185_s1_ul rev185_s1_ur
    (by decide) rev185_s1_ll_mem rev185_s1_lr_mem rev185_s1_ul_mem rev185_s1_ur_mem p
    (hp _ rev185_plane67_mem) (hp _ rev185_plane38_mem) hx0 hx1
def rev185_s2_ll : FractionPoint := ⟨383371739447,1659244000000,1275872260553,1659244000000⟩
theorem rev185_s2_ll_mem : rev185_s2_ll.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane12 rev185_vertex2 rev185_vertex3 rev185_s2_ll
    rev185_vertex2_mem rev185_vertex3_mem (by decide)
def rev185_s2_lr : FractionPoint := ⟨247349711339380133,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev185_s2_lr_mem : rev185_s2_lr.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane12 rev185_vertex2 rev185_vertex3 rev185_s2_lr
    rev185_vertex2_mem rev185_vertex3_mem (by decide)
def rev185_s2_ul : FractionPoint := ⟨383371739447,1659244000000,54273675950574103,58017457552800000⟩
theorem rev185_s2_ul_mem : rev185_s2_ul.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane38 rev185_vertex0 rev185_vertex5 rev185_s2_ul
    rev185_vertex0_mem rev185_vertex5_mem (by decide)
def rev185_s2_ur : FractionPoint := ⟨247349711339380133,1063994749732000000,173204894187558519860321,186019266090395292000000⟩
theorem rev185_s2_ur_mem : rev185_s2_ur.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane38 rev185_vertex0 rev185_vertex5 rev185_s2_ur
    rev185_vertex0_mem rev185_vertex5_mem (by decide)
theorem rev185_slab2 (p : Point) (hp : p∈IntegerCarrier rev185_planes)
    (hx0 : rev185_s2_ll.real.1≤p.1) (hx1 : p.1≤rev185_s2_lr.real.1) :
    p∈rationalHull (fractionRow185.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev185_plane12 rev185_plane38 rev185_s2_ll rev185_s2_lr rev185_s2_ul rev185_s2_ur
    (by decide) rev185_s2_ll_mem rev185_s2_lr_mem rev185_s2_ul_mem rev185_s2_ur_mem p
    (hp _ rev185_plane12_mem) (hp _ rev185_plane38_mem) hx0 hx1
def rev185_s3_ll : FractionPoint := ⟨247349711339380133,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev185_s3_ll_mem : rev185_s3_ll.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane34 rev185_vertex3 rev185_vertex4 rev185_s3_ll
    rev185_vertex3_mem rev185_vertex4_mem (by decide)
def rev185_s3_lr : FractionPoint := ⟨7515963822126429,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev185_s3_lr_mem : rev185_s3_lr.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane34 rev185_vertex3 rev185_vertex4 rev185_s3_lr
    rev185_vertex3_mem rev185_vertex4_mem (by decide)
def rev185_s3_ul : FractionPoint := ⟨247349711339380133,1063994749732000000,173204894187558519860321,186019266090395292000000⟩
theorem rev185_s3_ul_mem : rev185_s3_ul.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane38 rev185_vertex0 rev185_vertex5 rev185_s3_ul
    rev185_vertex0_mem rev185_vertex5_mem (by decide)
def rev185_s3_ur : FractionPoint := ⟨7515963822126429,32183417026000000,10441417088671251298091,11253317964145212000000⟩
theorem rev185_s3_ur_mem : rev185_s3_ur.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane38 rev185_vertex0 rev185_vertex5 rev185_s3_ur
    rev185_vertex0_mem rev185_vertex5_mem (by decide)
theorem rev185_slab3 (p : Point) (hp : p∈IntegerCarrier rev185_planes)
    (hx0 : rev185_s3_ll.real.1≤p.1) (hx1 : p.1≤rev185_s3_lr.real.1) :
    p∈rationalHull (fractionRow185.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev185_plane34 rev185_plane38 rev185_s3_ll rev185_s3_lr rev185_s3_ul rev185_s3_ur
    (by decide) rev185_s3_ll_mem rev185_s3_lr_mem rev185_s3_ul_mem rev185_s3_ur_mem p
    (hp _ rev185_plane34_mem) (hp _ rev185_plane38_mem) hx0 hx1
def rev185_s4_ll : FractionPoint := ⟨7515963822126429,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev185_s4_ll_mem : rev185_s4_ll.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane17 rev185_vertex4 rev185_vertex5 rev185_s4_ll
    rev185_vertex4_mem rev185_vertex5_mem (by decide)
def rev185_s4_lr : FractionPoint := ⟨2493941952605707,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev185_s4_lr_mem : rev185_s4_lr.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane17 rev185_vertex4 rev185_vertex5 rev185_s4_lr
    rev185_vertex4_mem rev185_vertex5_mem (by decide)
def rev185_s4_ul : FractionPoint := ⟨7515963822126429,32183417026000000,10441417088671251298091,11253317964145212000000⟩
theorem rev185_s4_ul_mem : rev185_s4_ul.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane38 rev185_vertex0 rev185_vertex5 rev185_s4_ul
    rev185_vertex0_mem rev185_vertex5_mem (by decide)
def rev185_s4_ur : FractionPoint := ⟨2493941952605707,9972624314000000,10496302777651103,11967149176800000⟩
theorem rev185_s4_ur_mem : rev185_s4_ur.real ∈ rationalHull (fractionRow185.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow185 rev185_plane38 rev185_vertex0 rev185_vertex5 rev185_s4_ur
    rev185_vertex0_mem rev185_vertex5_mem (by decide)
theorem rev185_slab4 (p : Point) (hp : p∈IntegerCarrier rev185_planes)
    (hx0 : rev185_s4_ll.real.1≤p.1) (hx1 : p.1≤rev185_s4_lr.real.1) :
    p∈rationalHull (fractionRow185.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev185_plane17 rev185_plane38 rev185_s4_ll rev185_s4_lr rev185_s4_ul rev185_s4_ur
    (by decide) rev185_s4_ll_mem rev185_s4_lr_mem rev185_s4_ul_mem rev185_s4_ur_mem p
    (hp _ rev185_plane17_mem) (hp _ rev185_plane38_mem) hx0 hx1
theorem rev185_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev185_planes) : rev185_s0_ll.real.1≤p.1 := by
  have hc := rev185_plane3.combine_sound rev185_plane67 202532000000 1 (by decide) (by decide) p
    (hp _ rev185_plane3_mem) (hp _ rev185_plane67_mem)
  exact (rev185_plane3.combine rev185_plane67 202532000000 1).xBoundCheck_sound rev185_s0_ll.nx rev185_s0_ll.dx true (by decide) p hc
theorem rev185_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev185_planes) : p.1≤rev185_s4_lr.real.1 := by
  have hc := rev185_plane17.combine_sound rev185_plane38 699324000000 287616000000 (by decide) (by decide) p
    (hp _ rev185_plane17_mem) (hp _ rev185_plane38_mem)
  exact (rev185_plane17.combine rev185_plane38 699324000000 287616000000).xBoundCheck_sound rev185_s4_lr.nx rev185_s4_lr.dx false (by decide) p hc
theorem rev185_hull (p : Point) (hp : p∈IntegerCarrier rev185_planes) :
    p∈rationalHull (fractionRow185.map FractionPoint.rational) := by
  have hxlo := rev185_bound0_lo p hp
  have hxhi := rev185_bound0_hi p hp
  by_cases h0 : p.1≤rev185_s0_lr.real.1
  · exact rev185_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev185_s1_lr.real.1
  · exact rev185_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev185_s2_lr.real.1
  · exact rev185_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev185_s3_lr.real.1
  · exact rev185_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev185_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull185 (p : Point)
    (hp : ∀ g, ClosedCell ((![12,15,0,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow185 := by
  rw [← fractionRow185_correct]
  exact rev185_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull185
