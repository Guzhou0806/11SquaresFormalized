import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks18
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev148_planes : List IntegerPlane := integerOverlayPlanes ![10,8,13,10]
def rev148_plane15 : IntegerPlane := ⟨2144520000000,(-699568000000),1185942108648⟩
theorem rev148_plane15_mem : rev148_plane15 ∈ rev148_planes := by decide
def rev148_plane19 : IntegerPlane := ⟨2129316000000,1440116000000,2741459880216⟩
theorem rev148_plane19_mem : rev148_plane19 ∈ rev148_planes := by decide
def rev148_plane33 : IntegerPlane := ⟨(-2044968000000),(-643972000000),(-1962432524019)⟩
theorem rev148_plane33_mem : rev148_plane33 ∈ rev148_planes := by decide
def rev148_plane37 : IntegerPlane := ⟨(-2058052000000),1574160000000,(-367887499047)⟩
theorem rev148_plane37_mem : rev148_plane37 ∈ rev148_planes := by decide
def rev148_plane52 : IntegerPlane := ⟨(-1574160000000),2058052000000,367887499047⟩
theorem rev148_plane52_mem : rev148_plane52 ∈ rev148_planes := by decide
def rev148_plane56 : IntegerPlane := ⟨287616000000,1855520000000,1643759759600⟩
theorem rev148_plane56_mem : rev148_plane56 ∈ rev148_planes := by decide
def rev148_vertex0 : FractionPoint := fractionRow148[0]!
theorem rev148_vertex0_mem : rev148_vertex0∈fractionRow148 := by decide
def rev148_vertex1 : FractionPoint := fractionRow148[1]!
theorem rev148_vertex1_mem : rev148_vertex1∈fractionRow148 := by decide
def rev148_vertex2 : FractionPoint := fractionRow148[2]!
theorem rev148_vertex2_mem : rev148_vertex2∈fractionRow148 := by decide
def rev148_vertex3 : FractionPoint := fractionRow148[3]!
theorem rev148_vertex3_mem : rev148_vertex3∈fractionRow148 := by decide
def rev148_vertex4 : FractionPoint := fractionRow148[4]!
theorem rev148_vertex4_mem : rev148_vertex4∈fractionRow148 := by decide
def rev148_vertex5 : FractionPoint := fractionRow148[5]!
theorem rev148_vertex5_mem : rev148_vertex5∈fractionRow148 := by decide
def rev148_s0_ll : FractionPoint := ⟨118789001090930133,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev148_s0_ll_mem : rev148_s0_ll.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane33 rev148_vertex5 rev148_vertex0 rev148_s0_ll
    rev148_vertex5_mem rev148_vertex0_mem (by decide)
def rev148_s0_lr : FractionPoint := ⟨1935297561189487,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev148_s0_lr_mem : rev148_s0_lr.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane33 rev148_vertex5 rev148_vertex0 rev148_s0_lr
    rev148_vertex5_mem rev148_vertex0_mem (by decide)
def rev148_s0_ul : FractionPoint := ⟨118789001090930133,162301238908000000,821617504442801373,1136108672356000000⟩
theorem rev148_s0_ul_mem : rev148_s0_ul.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane37 rev148_vertex5 rev148_vertex4 rev148_s0_ul
    rev148_vertex5_mem rev148_vertex4_mem (by decide)
def rev148_s0_ur : FractionPoint := ⟨1935297561189487,2546743666000000,1523013929201308906511,2004491004635280000000⟩
theorem rev148_s0_ur_mem : rev148_s0_ur.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane37 rev148_vertex5 rev148_vertex4 rev148_s0_ur
    rev148_vertex5_mem rev148_vertex4_mem (by decide)
theorem rev148_slab0 (p : Point) (hp : p∈IntegerCarrier rev148_planes)
    (hx0 : rev148_s0_ll.real.1≤p.1) (hx1 : p.1≤rev148_s0_lr.real.1) :
    p∈rationalHull (fractionRow148.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev148_plane33 rev148_plane37 rev148_s0_ll rev148_s0_lr rev148_s0_ul rev148_s0_ur
    (by decide) rev148_s0_ll_mem rev148_s0_lr_mem rev148_s0_ul_mem rev148_s0_ur_mem p
    (hp _ rev148_plane33_mem) (hp _ rev148_plane37_mem) hx0 hx1
def rev148_s1_ll : FractionPoint := ⟨1935297561189487,2546743666000000,3230547344875983,5093487332000000⟩
theorem rev148_s1_ll_mem : rev148_s1_ll.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane15 rev148_vertex0 rev148_vertex1 rev148_s1_ll
    rev148_vertex0_mem rev148_vertex1_mem (by decide)
def rev148_s1_lr : FractionPoint := ⟨367887499047,483892000000,1168881525099861,1839757384000000⟩
theorem rev148_s1_lr_mem : rev148_s1_lr.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane15 rev148_vertex0 rev148_vertex1 rev148_s1_lr
    rev148_vertex0_mem rev148_vertex1_mem (by decide)
def rev148_s1_ul : FractionPoint := ⟨1935297561189487,2546743666000000,1523013929201308906511,2004491004635280000000⟩
theorem rev148_s1_ul_mem : rev148_s1_ul.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane37 rev148_vertex5 rev148_vertex4 rev148_s1_ul
    rev148_vertex5_mem rev148_vertex4_mem (by decide)
def rev148_s1_ur : FractionPoint := ⟨367887499047,483892000000,367887499047,483892000000⟩
theorem rev148_s1_ur_mem : rev148_s1_ur.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane37 rev148_vertex5 rev148_vertex4 rev148_s1_ur
    rev148_vertex5_mem rev148_vertex4_mem (by decide)
theorem rev148_slab1 (p : Point) (hp : p∈IntegerCarrier rev148_planes)
    (hx0 : rev148_s1_ll.real.1≤p.1) (hx1 : p.1≤rev148_s1_lr.real.1) :
    p∈rationalHull (fractionRow148.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev148_plane15 rev148_plane37 rev148_s1_ll rev148_s1_lr rev148_s1_ul rev148_s1_ur
    (by decide) rev148_s1_ll_mem rev148_s1_lr_mem rev148_s1_ul_mem rev148_s1_ur_mem p
    (hp _ rev148_plane15_mem) (hp _ rev148_plane37_mem) hx0 hx1
def rev148_s2_ll : FractionPoint := ⟨367887499047,483892000000,1168881525099861,1839757384000000⟩
theorem rev148_s2_ll_mem : rev148_s2_ll.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane15 rev148_vertex0 rev148_vertex1 rev148_s2_ll
    rev148_vertex0_mem rev148_vertex1_mem (by decide)
def rev148_s2_lr : FractionPoint := ⟨16877002803328811,21955087795200000,13141313323503163293,19874581856512000000⟩
theorem rev148_s2_lr_mem : rev148_s2_lr.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane15 rev148_vertex0 rev148_vertex1 rev148_s2_lr
    rev148_vertex0_mem rev148_vertex1_mem (by decide)
def rev148_s2_ul : FractionPoint := ⟨367887499047,483892000000,367887499047,483892000000⟩
theorem rev148_s2_ul_mem : rev148_s2_ul.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane52 rev148_vertex4 rev148_vertex3 rev148_s2_ul
    rev148_vertex4_mem rev148_vertex3_mem (by decide)
def rev148_s2_ur : FractionPoint := ⟨16877002803328811,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev148_s2_ur_mem : rev148_s2_ur.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane52 rev148_vertex4 rev148_vertex3 rev148_s2_ur
    rev148_vertex4_mem rev148_vertex3_mem (by decide)
theorem rev148_slab2 (p : Point) (hp : p∈IntegerCarrier rev148_planes)
    (hx0 : rev148_s2_ll.real.1≤p.1) (hx1 : p.1≤rev148_s2_lr.real.1) :
    p∈rationalHull (fractionRow148.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev148_plane15 rev148_plane52 rev148_s2_ll rev148_s2_lr rev148_s2_ul rev148_s2_ur
    (by decide) rev148_s2_ll_mem rev148_s2_lr_mem rev148_s2_ul_mem rev148_s2_ur_mem p
    (hp _ rev148_plane15_mem) (hp _ rev148_plane52_mem) hx0 hx1
def rev148_s3_ll : FractionPoint := ⟨16877002803328811,21955087795200000,13141313323503163293,19874581856512000000⟩
theorem rev148_s3_ll_mem : rev148_s3_ll.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane15 rev148_vertex0 rev148_vertex1 rev148_s3_ll
    rev148_vertex0_mem rev148_vertex1_mem (by decide)
def rev148_s3_lr : FractionPoint := ⟨8498840334319621,11052462565200000,6623126699571354093,10005110160212000000⟩
theorem rev148_s3_lr_mem : rev148_s3_lr.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane15 rev148_vertex0 rev148_vertex1 rev148_s3_lr
    rev148_vertex0_mem rev148_vertex1_mem (by decide)
def rev148_s3_ul : FractionPoint := ⟨16877002803328811,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev148_s3_ul_mem : rev148_s3_ul.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane56 rev148_vertex3 rev148_vertex2 rev148_s3_ul
    rev148_vertex3_mem rev148_vertex2_mem (by decide)
def rev148_s3_ur : FractionPoint := ⟨8498840334319621,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev148_s3_ur_mem : rev148_s3_ur.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane56 rev148_vertex3 rev148_vertex2 rev148_s3_ur
    rev148_vertex3_mem rev148_vertex2_mem (by decide)
theorem rev148_slab3 (p : Point) (hp : p∈IntegerCarrier rev148_planes)
    (hx0 : rev148_s3_ll.real.1≤p.1) (hx1 : p.1≤rev148_s3_lr.real.1) :
    p∈rationalHull (fractionRow148.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev148_plane15 rev148_plane56 rev148_s3_ll rev148_s3_lr rev148_s3_ul rev148_s3_ur
    (by decide) rev148_s3_ll_mem rev148_s3_lr_mem rev148_s3_ul_mem rev148_s3_ur_mem p
    (hp _ rev148_plane15_mem) (hp _ rev148_plane56_mem) hx0 hx1
def rev148_s4_ll : FractionPoint := ⟨8498840334319621,11052462565200000,6623126699571354093,10005110160212000000⟩
theorem rev148_s4_ll_mem : rev148_s4_ll.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane15 rev148_vertex0 rev148_vertex1 rev148_s4_ll
    rev148_vertex0_mem rev148_vertex1_mem (by decide)
def rev148_s4_lr : FractionPoint := ⟨1642088682618057,2073350951000000,216994696901067,296192993000000⟩
theorem rev148_s4_lr_mem : rev148_s4_lr.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane15 rev148_vertex0 rev148_vertex1 rev148_s4_lr
    rev148_vertex0_mem rev148_vertex1_mem (by decide)
def rev148_s4_ul : FractionPoint := ⟨8498840334319621,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev148_s4_ul_mem : rev148_s4_ul.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane19 rev148_vertex2 rev148_vertex1 rev148_s4_ul
    rev148_vertex2_mem rev148_vertex1_mem (by decide)
def rev148_s4_ur : FractionPoint := ⟨1642088682618057,2073350951000000,216994696901067,296192993000000⟩
theorem rev148_s4_ur_mem : rev148_s4_ur.real ∈ rationalHull (fractionRow148.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow148 rev148_plane19 rev148_vertex2 rev148_vertex1 rev148_s4_ur
    rev148_vertex2_mem rev148_vertex1_mem (by decide)
theorem rev148_slab4 (p : Point) (hp : p∈IntegerCarrier rev148_planes)
    (hx0 : rev148_s4_ll.real.1≤p.1) (hx1 : p.1≤rev148_s4_lr.real.1) :
    p∈rationalHull (fractionRow148.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev148_plane15 rev148_plane19 rev148_s4_ll rev148_s4_lr rev148_s4_ul rev148_s4_ur
    (by decide) rev148_s4_ll_mem rev148_s4_lr_mem rev148_s4_ul_mem rev148_s4_ur_mem p
    (hp _ rev148_plane15_mem) (hp _ rev148_plane19_mem) hx0 hx1
theorem rev148_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev148_planes) : rev148_s0_ll.real.1≤p.1 := by
  have hc := rev148_plane33.combine_sound rev148_plane37 1574160000000 643972000000 (by decide) (by decide) p
    (hp _ rev148_plane33_mem) (hp _ rev148_plane37_mem)
  exact (rev148_plane33.combine rev148_plane37 1574160000000 643972000000).xBoundCheck_sound rev148_s0_ll.nx rev148_s0_ll.dx true (by decide) p hc
theorem rev148_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev148_planes) : p.1≤rev148_s4_lr.real.1 := by
  have hc := rev148_plane15.combine_sound rev148_plane19 1440116000000 699568000000 (by decide) (by decide) p
    (hp _ rev148_plane15_mem) (hp _ rev148_plane19_mem)
  exact (rev148_plane15.combine rev148_plane19 1440116000000 699568000000).xBoundCheck_sound rev148_s4_lr.nx rev148_s4_lr.dx false (by decide) p hc
theorem rev148_hull (p : Point) (hp : p∈IntegerCarrier rev148_planes) :
    p∈rationalHull (fractionRow148.map FractionPoint.rational) := by
  have hxlo := rev148_bound0_lo p hp
  have hxhi := rev148_bound0_hi p hp
  by_cases h0 : p.1≤rev148_s0_lr.real.1
  · exact rev148_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev148_s1_lr.real.1
  · exact rev148_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p.1≤rev148_s2_lr.real.1
  · exact rev148_slab2 p hp (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p.1≤rev148_s3_lr.real.1
  · exact rev148_slab3 p hp (le_of_lt (lt_of_not_ge h2)) h3
  exact rev148_slab4 p hp (le_of_lt (lt_of_not_ge h3)) hxhi
theorem overlay_in_hull148 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,8,13,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow148 := by
  rw [← fractionRow148_correct]
  exact rev148_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull148
