import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks26
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev210_planes : List IntegerPlane := integerOverlayPlanes ![15,8,12,10]
def rev210_plane14 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-2741459880216)⟩
theorem rev210_plane14_mem : rev210_plane14 ∈ rev210_planes := by decide
def rev210_plane52 : IntegerPlane := ⟨(-1861776000000),202532000000,(-1275872260553)⟩
theorem rev210_plane52_mem : rev210_plane52 ∈ rev210_planes := by decide
def rev210_plane57 : IntegerPlane := ⟨(-287616000000),(-1855520000000),(-1643759759600)⟩
theorem rev210_plane57_mem : rev210_plane57 ∈ rev210_planes := by decide
def rev210_plane79 : IntegerPlane := ⟨1440116000000,2129316000000,2741459880216⟩
theorem rev210_plane79_mem : rev210_plane79 ∈ rev210_planes := by decide
def rev210_vertex0 : FractionPoint := fractionRow210[0]!
theorem rev210_vertex0_mem : rev210_vertex0∈fractionRow210 := by decide
def rev210_vertex1 : FractionPoint := fractionRow210[1]!
theorem rev210_vertex1_mem : rev210_vertex1∈fractionRow210 := by decide
def rev210_vertex2 : FractionPoint := fractionRow210[2]!
theorem rev210_vertex2_mem : rev210_vertex2∈fractionRow210 := by decide
def rev210_vertex3 : FractionPoint := fractionRow210[3]!
theorem rev210_vertex3_mem : rev210_vertex3∈fractionRow210 := by decide
def rev210_s0_ll : FractionPoint := ⟨119631870441922553,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev210_s0_ll_mem : rev210_s0_ll.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane14 rev210_vertex1 rev210_vertex2 rev210_s0_ll
    rev210_vertex1_mem rev210_vertex2_mem (by decide)
def rev210_s0_lr : FractionPoint := ⟨163598428540578933,212798949946400000,293783790454796190400743,383068965751262228000000⟩
theorem rev210_s0_lr_mem : rev210_s0_lr.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane14 rev210_vertex1 rev210_vertex2 rev210_s0_lr
    rev210_vertex1_mem rev210_vertex2_mem (by decide)
def rev210_s0_ul : FractionPoint := ⟨119631870441922553,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev210_s0_ul_mem : rev210_s0_ul.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane52 rev210_vertex1 rev210_vertex0 rev210_s0_ul
    rev210_vertex1_mem rev210_vertex0_mem (by decide)
def rev210_s0_ur : FractionPoint := ⟨163598428540578933,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev210_s0_ur_mem : rev210_s0_ur.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane52 rev210_vertex1 rev210_vertex0 rev210_s0_ur
    rev210_vertex1_mem rev210_vertex0_mem (by decide)
theorem rev210_slab0 (p : Point) (hp : p∈IntegerCarrier rev210_planes)
    (hx0 : rev210_s0_ll.real.1≤p.1) (hx1 : p.1≤rev210_s0_lr.real.1) :
    p∈rationalHull (fractionRow210.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev210_plane14 rev210_plane52 rev210_s0_ll rev210_s0_lr rev210_s0_ul rev210_s0_ur
    (by decide) rev210_s0_ll_mem rev210_s0_lr_mem rev210_s0_ul_mem rev210_s0_ur_mem p
    (hp _ rev210_plane14_mem) (hp _ rev210_plane52_mem) hx0 hx1
def rev210_s1_ll : FractionPoint := ⟨163598428540578933,212798949946400000,293783790454796190400743,383068965751262228000000⟩
theorem rev210_s1_ll_mem : rev210_s1_ll.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane14 rev210_vertex1 rev210_vertex2 rev210_s1_ll
    rev210_vertex1_mem rev210_vertex2_mem (by decide)
def rev210_s1_lr : FractionPoint := ⟨8498840334319621,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev210_s1_lr_mem : rev210_s1_lr.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane14 rev210_vertex1 rev210_vertex2 rev210_s1_lr
    rev210_vertex1_mem rev210_vertex2_mem (by decide)
def rev210_s1_ul : FractionPoint := ⟨163598428540578933,212798949946400000,816645038392619867,1063994749732000000⟩
theorem rev210_s1_ul_mem : rev210_s1_ul.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane79 rev210_vertex0 rev210_vertex3 rev210_s1_ul
    rev210_vertex0_mem rev210_vertex3_mem (by decide)
def rev210_s1_ur : FractionPoint := ⟨8498840334319621,11052462565200000,22575708441482475967559,29417731724351754000000⟩
theorem rev210_s1_ur_mem : rev210_s1_ur.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane79 rev210_vertex0 rev210_vertex3 rev210_s1_ur
    rev210_vertex0_mem rev210_vertex3_mem (by decide)
theorem rev210_slab1 (p : Point) (hp : p∈IntegerCarrier rev210_planes)
    (hx0 : rev210_s1_ll.real.1≤p.1) (hx1 : p.1≤rev210_s1_lr.real.1) :
    p∈rationalHull (fractionRow210.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev210_plane14 rev210_plane79 rev210_s1_ll rev210_s1_lr rev210_s1_ul rev210_s1_ur
    (by decide) rev210_s1_ll_mem rev210_s1_lr_mem rev210_s1_ul_mem rev210_s1_ur_mem p
    (hp _ rev210_plane14_mem) (hp _ rev210_plane79_mem) hx0 hx1
def rev210_s2_ll : FractionPoint := ⟨8498840334319621,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev210_s2_ll_mem : rev210_s2_ll.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane57 rev210_vertex2 rev210_vertex3 rev210_s2_ll
    rev210_vertex2_mem rev210_vertex3_mem (by decide)
def rev210_s2_lr : FractionPoint := ⟨4958592752081121,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev210_s2_lr_mem : rev210_s2_lr.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane57 rev210_vertex2 rev210_vertex3 rev210_s2_lr
    rev210_vertex2_mem rev210_vertex3_mem (by decide)
def rev210_s2_ul : FractionPoint := ⟨8498840334319621,11052462565200000,22575708441482475967559,29417731724351754000000⟩
theorem rev210_s2_ul_mem : rev210_s2_ul.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane79 rev210_vertex0 rev210_vertex3 rev210_s2_ul
    rev210_vertex0_mem rev210_vertex3_mem (by decide)
def rev210_s2_ur : FractionPoint := ⟨4958592752081121,6436683405200000,24667453203873571,32183417026000000⟩
theorem rev210_s2_ur_mem : rev210_s2_ur.real ∈ rationalHull (fractionRow210.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow210 rev210_plane79 rev210_vertex0 rev210_vertex3 rev210_s2_ur
    rev210_vertex0_mem rev210_vertex3_mem (by decide)
theorem rev210_slab2 (p : Point) (hp : p∈IntegerCarrier rev210_planes)
    (hx0 : rev210_s2_ll.real.1≤p.1) (hx1 : p.1≤rev210_s2_lr.real.1) :
    p∈rationalHull (fractionRow210.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev210_plane57 rev210_plane79 rev210_s2_ll rev210_s2_lr rev210_s2_ul rev210_s2_ur
    (by decide) rev210_s2_ll_mem rev210_s2_lr_mem rev210_s2_ul_mem rev210_s2_ur_mem p
    (hp _ rev210_plane57_mem) (hp _ rev210_plane79_mem) hx0 hx1
theorem rev210_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev210_planes) : rev210_s0_ll.real.1≤p.1 := by
  have hc := rev210_plane14.combine_sound rev210_plane52 202532000000 1440116000000 (by decide) (by decide) p
    (hp _ rev210_plane14_mem) (hp _ rev210_plane52_mem)
  exact (rev210_plane14.combine rev210_plane52 202532000000 1440116000000).xBoundCheck_sound rev210_s0_ll.nx rev210_s0_ll.dx true (by decide) p hc
theorem rev210_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev210_planes) : p.1≤rev210_s2_lr.real.1 := by
  have hc := rev210_plane57.combine_sound rev210_plane79 2129316000000 1855520000000 (by decide) (by decide) p
    (hp _ rev210_plane57_mem) (hp _ rev210_plane79_mem)
  exact (rev210_plane57.combine rev210_plane79 2129316000000 1855520000000).xBoundCheck_sound rev210_s2_lr.nx rev210_s2_lr.dx false (by decide) p hc
theorem rev210_hull (p : Point) (hp : p∈IntegerCarrier rev210_planes) :
    p∈rationalHull (fractionRow210.map FractionPoint.rational) := by
  have hxlo := rev210_bound0_lo p hp
  have hxhi := rev210_bound0_hi p hp
  by_cases h0 : p.1≤rev210_s0_lr.real.1
  · exact rev210_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev210_s1_lr.real.1
  · exact rev210_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev210_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull210 (p : Point)
    (hp : ∀ g, ClosedCell ((![15,8,12,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow210 := by
  rw [← fractionRow210_correct]
  exact rev210_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull210
