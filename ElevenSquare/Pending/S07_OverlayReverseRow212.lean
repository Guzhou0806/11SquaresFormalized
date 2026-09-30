import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks26
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev212_planes : List IntegerPlane := integerOverlayPlanes ![15,8,12,15]
def rev212_plane1 : IntegerPlane := ⟨1,0,1⟩
theorem rev212_plane1_mem : rev212_plane1 ∈ rev212_planes := by decide
def rev212_plane36 : IntegerPlane := ⟨(-202532000000),1861776000000,1275872260553⟩
theorem rev212_plane36_mem : rev212_plane36 ∈ rev212_planes := by decide
def rev212_plane52 : IntegerPlane := ⟨(-1861776000000),202532000000,(-1275872260553)⟩
theorem rev212_plane52_mem : rev212_plane52 ∈ rev212_planes := by decide
def rev212_plane57 : IntegerPlane := ⟨(-287616000000),(-1855520000000),(-1643759759600)⟩
theorem rev212_plane57_mem : rev212_plane57 ∈ rev212_planes := by decide
def rev212_plane74 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-2741459880216)⟩
theorem rev212_plane74_mem : rev212_plane74 ∈ rev212_planes := by decide
def rev212_plane78 : IntegerPlane := ⟨699324000000,(-2145688000000),(-995724727641)⟩
theorem rev212_plane78_mem : rev212_plane78 ∈ rev212_planes := by decide
def rev212_vertex0 : FractionPoint := fractionRow212[0]!
theorem rev212_vertex0_mem : rev212_vertex0∈fractionRow212 := by decide
def rev212_vertex1 : FractionPoint := fractionRow212[1]!
theorem rev212_vertex1_mem : rev212_vertex1∈fractionRow212 := by decide
def rev212_vertex2 : FractionPoint := fractionRow212[2]!
theorem rev212_vertex2_mem : rev212_vertex2∈fractionRow212 := by decide
def rev212_vertex3 : FractionPoint := fractionRow212[3]!
theorem rev212_vertex3_mem : rev212_vertex3∈fractionRow212 := by decide
def rev212_vertex4 : FractionPoint := fractionRow212[4]!
theorem rev212_vertex4_mem : rev212_vertex4∈fractionRow212 := by decide
def rev212_vertex5 : FractionPoint := fractionRow212[5]!
theorem rev212_vertex5_mem : rev212_vertex5∈fractionRow212 := by decide
def rev212_s0_ll : FractionPoint := ⟨163598428540578933,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev212_s0_ll_mem : rev212_s0_ll.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane74 rev212_vertex3 rev212_vertex4 rev212_s0_ll
    rev212_vertex3_mem rev212_vertex4_mem (by decide)
def rev212_s0_lr : FractionPoint := ⟨1275872260553,1659244000000,677836700277643139,883263699276000000⟩
theorem rev212_s0_lr_mem : rev212_s0_lr.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane74 rev212_vertex3 rev212_vertex4 rev212_s0_lr
    rev212_vertex3_mem rev212_vertex4_mem (by decide)
def rev212_s0_ul : FractionPoint := ⟨163598428540578933,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev212_s0_ul_mem : rev212_s0_ul.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane52 rev212_vertex3 rev212_vertex2 rev212_s0_ul
    rev212_vertex3_mem rev212_vertex2_mem (by decide)
def rev212_s0_ur : FractionPoint := ⟨1275872260553,1659244000000,1275872260553,1659244000000⟩
theorem rev212_s0_ur_mem : rev212_s0_ur.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane52 rev212_vertex3 rev212_vertex2 rev212_s0_ur
    rev212_vertex3_mem rev212_vertex2_mem (by decide)
theorem rev212_slab0 (p : Point) (hp : p∈IntegerCarrier rev212_planes)
    (hx0 : rev212_s0_ll.real.1≤p.1) (hx1 : p.1≤rev212_s0_lr.real.1) :
    p∈rationalHull (fractionRow212.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev212_plane74 rev212_plane52 rev212_s0_ll rev212_s0_lr rev212_s0_ul rev212_s0_ur
    (by decide) rev212_s0_ll_mem rev212_s0_lr_mem rev212_s0_ul_mem rev212_s0_ur_mem p
    (hp _ rev212_plane74_mem) (hp _ rev212_plane52_mem) hx0 hx1
def rev212_s1_ll : FractionPoint := ⟨1275872260553,1659244000000,677836700277643139,883263699276000000⟩
theorem rev212_s1_ll_mem : rev212_s1_ll.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane74 rev212_vertex3 rev212_vertex4 rev212_s1_ll
    rev212_vertex3_mem rev212_vertex4_mem (by decide)
def rev212_s1_lr : FractionPoint := ⟨4958592752081121,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev212_s1_lr_mem : rev212_s1_lr.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane74 rev212_vertex3 rev212_vertex4 rev212_s1_lr
    rev212_vertex3_mem rev212_vertex4_mem (by decide)
def rev212_s1_ul : FractionPoint := ⟨1275872260553,1659244000000,1275872260553,1659244000000⟩
theorem rev212_s1_ul_mem : rev212_s1_ul.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane36 rev212_vertex2 rev212_vertex1 rev212_s1_ul
    rev212_vertex2_mem rev212_vertex1_mem (by decide)
def rev212_s1_ur : FractionPoint := ⟨4958592752081121,6436683405200000,23041648784802498183619,29959156708499088000000⟩
theorem rev212_s1_ur_mem : rev212_s1_ur.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane36 rev212_vertex2 rev212_vertex1 rev212_s1_ur
    rev212_vertex2_mem rev212_vertex1_mem (by decide)
theorem rev212_slab1 (p : Point) (hp : p∈IntegerCarrier rev212_planes)
    (hx0 : rev212_s1_ll.real.1≤p.1) (hx1 : p.1≤rev212_s1_lr.real.1) :
    p∈rationalHull (fractionRow212.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev212_plane74 rev212_plane36 rev212_s1_ll rev212_s1_lr rev212_s1_ul rev212_s1_ur
    (by decide) rev212_s1_ll_mem rev212_s1_lr_mem rev212_s1_ul_mem rev212_s1_ur_mem p
    (hp _ rev212_plane74_mem) (hp _ rev212_plane36_mem) hx0 hx1
def rev212_s2_ll : FractionPoint := ⟨4958592752081121,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev212_s2_ll_mem : rev212_s2_ll.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane57 rev212_vertex4 rev212_vertex5 rev212_s2_ll
    rev212_vertex4_mem rev212_vertex5_mem (by decide)
def rev212_s2_lr : FractionPoint := ⟨10496302777651103,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev212_s2_lr_mem : rev212_s2_lr.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane57 rev212_vertex4 rev212_vertex5 rev212_s2_lr
    rev212_vertex4_mem rev212_vertex5_mem (by decide)
def rev212_s2_ul : FractionPoint := ⟨4958592752081121,6436683405200000,23041648784802498183619,29959156708499088000000⟩
theorem rev212_s2_ul_mem : rev212_s2_ul.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane36 rev212_vertex2 rev212_vertex1 rev212_s2_ul
    rev212_vertex2_mem rev212_vertex1_mem (by decide)
def rev212_s2_ur : FractionPoint := ⟨10496302777651103,11967149176800000,10871494291713763909729,13925094453616248000000⟩
theorem rev212_s2_ur_mem : rev212_s2_ur.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane36 rev212_vertex2 rev212_vertex1 rev212_s2_ur
    rev212_vertex2_mem rev212_vertex1_mem (by decide)
theorem rev212_slab2 (p : Point) (hp : p∈IntegerCarrier rev212_planes)
    (hx0 : rev212_s2_ll.real.1≤p.1) (hx1 : p.1≤rev212_s2_lr.real.1) :
    p∈rationalHull (fractionRow212.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev212_plane57 rev212_plane36 rev212_s2_ll rev212_s2_lr rev212_s2_ul rev212_s2_ur
    (by decide) rev212_s2_ll_mem rev212_s2_lr_mem rev212_s2_ul_mem rev212_s2_ur_mem p
    (hp _ rev212_plane57_mem) (hp _ rev212_plane36_mem) hx0 hx1
def rev212_s3_ll : FractionPoint := ⟨10496302777651103,11967149176800000,7478682361394293,9972624314000000⟩
theorem rev212_s3_ll_mem : rev212_s3_ll.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane78 rev212_vertex5 rev212_vertex0 rev212_s3_ll
    rev212_vertex5_mem rev212_vertex0_mem (by decide)
def rev212_s3_lr : FractionPoint := ⟨1,1,1695048727641,2145688000000⟩
theorem rev212_s3_lr_mem : rev212_s3_lr.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane78 rev212_vertex5 rev212_vertex0 rev212_s3_lr
    rev212_vertex5_mem rev212_vertex0_mem (by decide)
def rev212_s3_ul : FractionPoint := ⟨10496302777651103,11967149176800000,10871494291713763909729,13925094453616248000000⟩
theorem rev212_s3_ul_mem : rev212_s3_ul.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane36 rev212_vertex2 rev212_vertex1 rev212_s3_ul
    rev212_vertex2_mem rev212_vertex1_mem (by decide)
def rev212_s3_ur : FractionPoint := ⟨1,1,1478404260553,1861776000000⟩
theorem rev212_s3_ur_mem : rev212_s3_ur.real ∈ rationalHull (fractionRow212.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow212 rev212_plane36 rev212_vertex2 rev212_vertex1 rev212_s3_ur
    rev212_vertex2_mem rev212_vertex1_mem (by decide)
theorem rev212_slab3 (p : Point) (hp : p∈IntegerCarrier rev212_planes)
    (hx0 : rev212_s3_ll.real.1≤p.1) (hx1 : p.1≤rev212_s3_lr.real.1) :
    p∈rationalHull (fractionRow212.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev212_plane78 rev212_plane36 rev212_s3_ll rev212_s3_lr rev212_s3_ul rev212_s3_ur
    (by decide) rev212_s3_ll_mem rev212_s3_lr_mem rev212_s3_ul_mem rev212_s3_ur_mem p
    (hp _ rev212_plane78_mem) (hp _ rev212_plane36_mem) hx0 hx1
theorem rev212_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev212_planes) : rev212_s0_ll.real.1≤p.1 := by
  have hc := rev212_plane52.combine_sound rev212_plane74 2129316000000 202532000000 (by decide) (by decide) p
    (hp _ rev212_plane52_mem) (hp _ rev212_plane74_mem)
  exact (rev212_plane52.combine rev212_plane74 2129316000000 202532000000).xBoundCheck_sound rev212_s0_ll.nx rev212_s0_ll.dx true (by decide) p hc
theorem rev212_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev212_planes) : p.1≤rev212_s3_lr.real.1 := by
  have hc := rev212_plane1.combine_sound rev212_plane1 1 0 (by decide) (by decide) p
    (hp _ rev212_plane1_mem) (hp _ rev212_plane1_mem)
  exact (rev212_plane1.combine rev212_plane1 1 0).xBoundCheck_sound rev212_s3_lr.nx rev212_s3_lr.dx false (by decide) p hc
theorem rev212_hull (p : Point) (hp : p∈IntegerCarrier rev212_planes) :
    p∈rationalHull (fractionRow212.map FractionPoint.rational) := by
  have hxlo := rev212_bound0_lo p hp
  have hxhi := rev212_bound0_hi p hp
  by_cases h0 : p.1≤rev212_s0_lr.real.1
  · exact rev212_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev212_s1_lr.real.1
  · exact rev212_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev212_s2_lr.real.1
  · exact rev212_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  exact rev212_slab3 p hp (le_of_lt (lt_of_not_ge h2)) hxhi
theorem overlay_in_hull212 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,8,12,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow212 := by
  rw [← fractionRow212_correct]
  exact rev212_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull212
