import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks12
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev99_planes : List IntegerPlane := integerOverlayPlanes ![7,0,15,12]
def rev99_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev99_plane1_mem : rev99_plane1 ∈ rev99_planes := by decide
def rev99_plane7 : IntegerPlane := ⟨(-202532000000),(-1861776000000),(-585903739447)⟩
theorem rev99_plane7_mem : rev99_plane7 ∈ rev99_planes := by decide
def rev99_plane54 : IntegerPlane := ⟨(-1440116000000),2129316000000,(-612143880216)⟩
theorem rev99_plane54_mem : rev99_plane54 ∈ rev99_planes := by decide
def rev99_plane58 : IntegerPlane := ⟨699324000000,2145688000000,1149963272359⟩
theorem rev99_plane58_mem : rev99_plane58 ∈ rev99_planes := by decide
def rev99_plane72 : IntegerPlane := ⟨(-1861776000000),(-202532000000),(-1478404260553)⟩
theorem rev99_plane72_mem : rev99_plane72 ∈ rev99_planes := by decide
def rev99_plane77 : IntegerPlane := ⟨(-287616000000),1855520000000,211760240400⟩
theorem rev99_plane77_mem : rev99_plane77 ∈ rev99_planes := by decide
def rev99_vertex0 : FractionPoint := fractionRow99[0]!
theorem rev99_vertex0_mem : rev99_vertex0∈fractionRow99 := by decide
def rev99_vertex1 : FractionPoint := fractionRow99[1]!
theorem rev99_vertex1_mem : rev99_vertex1∈fractionRow99 := by decide
def rev99_vertex2 : FractionPoint := fractionRow99[2]!
theorem rev99_vertex2_mem : rev99_vertex2∈fractionRow99 := by decide
def rev99_vertex3 : FractionPoint := fractionRow99[3]!
theorem rev99_vertex3_mem : rev99_vertex3∈fractionRow99 := by decide
def rev99_vertex4 : FractionPoint := fractionRow99[4]!
theorem rev99_vertex4_mem : rev99_vertex4∈fractionRow99 := by decide
def rev99_vertex5 : FractionPoint := fractionRow99[5]!
theorem rev99_vertex5_mem : rev99_vertex5∈fractionRow99 := by decide
def rev99_s0_ll : FractionPoint := ⟨163598428540578933,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev99_s0_ll_mem : rev99_s0_ll.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane72 rev99_vertex4 rev99_vertex5 rev99_s0_ll
    rev99_vertex4_mem rev99_vertex5_mem (by decide)
def rev99_s0_lr : FractionPoint := ⟨1275872260553,1659244000000,383371739447,1659244000000⟩
theorem rev99_s0_lr_mem : rev99_s0_lr.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane72 rev99_vertex4 rev99_vertex5 rev99_s0_lr
    rev99_vertex4_mem rev99_vertex5_mem (by decide)
def rev99_s0_ul : FractionPoint := ⟨163598428540578933,212798949946400000,247349711339380133,1063994749732000000⟩
theorem rev99_s0_ul_mem : rev99_s0_ul.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane54 rev99_vertex4 rev99_vertex3 rev99_s0_ul
    rev99_vertex4_mem rev99_vertex3_mem (by decide)
def rev99_s0_ur : FractionPoint := ⟨1275872260553,1659244000000,205426998998356861,883263699276000000⟩
theorem rev99_s0_ur_mem : rev99_s0_ur.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane54 rev99_vertex4 rev99_vertex3 rev99_s0_ur
    rev99_vertex4_mem rev99_vertex3_mem (by decide)
theorem rev99_slab0 (p : Point) (hp : p∈IntegerCarrier rev99_planes)
    (hx0 : rev99_s0_ll.real.1≤p.1) (hx1 : p.1≤rev99_s0_lr.real.1) :
    p∈rationalHull (fractionRow99.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev99_plane72 rev99_plane54 rev99_s0_ll rev99_s0_lr rev99_s0_ul rev99_s0_ur
    (by decide) rev99_s0_ll_mem rev99_s0_lr_mem rev99_s0_ul_mem rev99_s0_ur_mem p
    (hp _ rev99_plane72_mem) (hp _ rev99_plane54_mem) hx0 hx1
def rev99_s1_ll : FractionPoint := ⟨1275872260553,1659244000000,383371739447,1659244000000⟩
theorem rev99_s1_ll_mem : rev99_s1_ll.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane7 rev99_vertex5 rev99_vertex0 rev99_s1_ll
    rev99_vertex5_mem rev99_vertex0_mem (by decide)
def rev99_s1_lr : FractionPoint := ⟨4958592752081121,6436683405200000,6917507923696589816381,29959156708499088000000⟩
theorem rev99_s1_lr_mem : rev99_s1_lr.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane7 rev99_vertex5 rev99_vertex0 rev99_s1_lr
    rev99_vertex5_mem rev99_vertex0_mem (by decide)
def rev99_s1_ul : FractionPoint := ⟨1275872260553,1659244000000,205426998998356861,883263699276000000⟩
theorem rev99_s1_ul_mem : rev99_s1_ul.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane54 rev99_vertex4 rev99_vertex3 rev99_s1_ul
    rev99_vertex4_mem rev99_vertex3_mem (by decide)
def rev99_s1_ur : FractionPoint := ⟨4958592752081121,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev99_s1_ur_mem : rev99_s1_ur.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane54 rev99_vertex4 rev99_vertex3 rev99_s1_ur
    rev99_vertex4_mem rev99_vertex3_mem (by decide)
theorem rev99_slab1 (p : Point) (hp : p∈IntegerCarrier rev99_planes)
    (hx0 : rev99_s1_ll.real.1≤p.1) (hx1 : p.1≤rev99_s1_lr.real.1) :
    p∈rationalHull (fractionRow99.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev99_plane7 rev99_plane54 rev99_s1_ll rev99_s1_lr rev99_s1_ul rev99_s1_ur
    (by decide) rev99_s1_ll_mem rev99_s1_lr_mem rev99_s1_ul_mem rev99_s1_ur_mem p
    (hp _ rev99_plane7_mem) (hp _ rev99_plane54_mem) hx0 hx1
def rev99_s2_ll : FractionPoint := ⟨4958592752081121,6436683405200000,6917507923696589816381,29959156708499088000000⟩
theorem rev99_s2_ll_mem : rev99_s2_ll.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane7 rev99_vertex5 rev99_vertex0 rev99_s2_ll
    rev99_vertex5_mem rev99_vertex0_mem (by decide)
def rev99_s2_lr : FractionPoint := ⟨10496302777651103,11967149176800000,3053600161902484090271,13925094453616248000000⟩
theorem rev99_s2_lr_mem : rev99_s2_lr.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane7 rev99_vertex5 rev99_vertex0 rev99_s2_lr
    rev99_vertex5_mem rev99_vertex0_mem (by decide)
def rev99_s2_ul : FractionPoint := ⟨4958592752081121,6436683405200000,7515963822126429,32183417026000000⟩
theorem rev99_s2_ul_mem : rev99_s2_ul.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane77 rev99_vertex3 rev99_vertex2 rev99_s2_ul
    rev99_vertex3_mem rev99_vertex2_mem (by decide)
def rev99_s2_ur : FractionPoint := ⟨10496302777651103,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev99_s2_ur_mem : rev99_s2_ur.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane77 rev99_vertex3 rev99_vertex2 rev99_s2_ur
    rev99_vertex3_mem rev99_vertex2_mem (by decide)
theorem rev99_slab2 (p : Point) (hp : p∈IntegerCarrier rev99_planes)
    (hx0 : rev99_s2_ll.real.1≤p.1) (hx1 : p.1≤rev99_s2_lr.real.1) :
    p∈rationalHull (fractionRow99.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev99_plane7 rev99_plane77 rev99_s2_ll rev99_s2_lr rev99_s2_ul rev99_s2_ur
    (by decide) rev99_s2_ll_mem rev99_s2_lr_mem rev99_s2_ul_mem rev99_s2_ur_mem p
    (hp _ rev99_plane7_mem) (hp _ rev99_plane77_mem) hx0 hx1
def rev99_s3_ll : FractionPoint := ⟨10496302777651103,11967149176800000,3053600161902484090271,13925094453616248000000⟩
theorem rev99_s3_ll_mem : rev99_s3_ll.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane7 rev99_vertex5 rev99_vertex0 rev99_s3_ll
    rev99_vertex5_mem rev99_vertex0_mem (by decide)
def rev99_s3_lr : FractionPoint := ⟨1,1,383371739447,1861776000000⟩
theorem rev99_s3_lr_mem : rev99_s3_lr.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane7 rev99_vertex5 rev99_vertex0 rev99_s3_lr
    rev99_vertex5_mem rev99_vertex0_mem (by decide)
def rev99_s3_ul : FractionPoint := ⟨10496302777651103,11967149176800000,2493941952605707,9972624314000000⟩
theorem rev99_s3_ul_mem : rev99_s3_ul.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane58 rev99_vertex2 rev99_vertex1 rev99_s3_ul
    rev99_vertex2_mem rev99_vertex1_mem (by decide)
def rev99_s3_ur : FractionPoint := ⟨1,1,450639272359,2145688000000⟩
theorem rev99_s3_ur_mem : rev99_s3_ur.real ∈ rationalHull (fractionRow99.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow99 rev99_plane58 rev99_vertex2 rev99_vertex1 rev99_s3_ur
    rev99_vertex2_mem rev99_vertex1_mem (by decide)
theorem rev99_slab3 (p : Point) (hp : p∈IntegerCarrier rev99_planes)
    (hx0 : rev99_s3_ll.real.1≤p.1) (hx1 : p.1≤rev99_s3_lr.real.1) :
    p∈rationalHull (fractionRow99.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev99_plane7 rev99_plane58 rev99_s3_ll rev99_s3_lr rev99_s3_ul rev99_s3_ur
    (by decide) rev99_s3_ll_mem rev99_s3_lr_mem rev99_s3_ul_mem rev99_s3_ur_mem p
    (hp _ rev99_plane7_mem) (hp _ rev99_plane58_mem) hx0 hx1
theorem rev99_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev99_planes) : rev99_s0_ll.real.1≤p.1 := by
  have hc := rev99_plane54.combine_sound rev99_plane72 202532000000 2129316000000 (by decide) (by decide) p
    (hp _ rev99_plane54_mem) (hp _ rev99_plane72_mem)
  exact (rev99_plane54.combine rev99_plane72 202532000000 2129316000000).xBoundCheck_sound rev99_s0_ll.nx rev99_s0_ll.dx true (by decide) p hc
theorem rev99_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev99_planes) : p.1≤rev99_s3_lr.real.1 := by
  have hc := rev99_plane1.combine_sound rev99_plane1 1 0 (by decide) (by decide) p
    (hp _ rev99_plane1_mem) (hp _ rev99_plane1_mem)
  exact (rev99_plane1.combine rev99_plane1 1 0).xBoundCheck_sound rev99_s3_lr.nx rev99_s3_lr.dx false (by decide) p hc
theorem rev99_hull (p : Point) (hp : p∈IntegerCarrier rev99_planes) :
    p∈rationalHull (fractionRow99.map FractionPoint.rational) := by
  have hxlo := rev99_bound0_lo p hp
  have hxhi := rev99_bound0_hi p hp
  by_cases h0 : p.1≤rev99_s0_lr.real.1
  · exact rev99_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev99_s1_lr.real.1
  · exact rev99_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev99_s2_lr.real.1
  · exact rev99_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev99_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull99 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,0,15,12] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow99 := by
  rw [← fractionRow99_correct]
  exact rev99_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull99
