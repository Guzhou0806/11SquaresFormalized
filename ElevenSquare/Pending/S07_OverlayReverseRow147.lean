import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks18
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev147_planes : List IntegerPlane := integerOverlayPlanes ![10,8,12,10]
def rev147_plane19 : IntegerPlane := ⟨2129316000000,1440116000000,2741459880216⟩
theorem rev147_plane19_mem : rev147_plane19 ∈ rev147_planes := by decide
def rev147_plane52 : IntegerPlane := ⟨(-1861776000000),202532000000,(-1275872260553)⟩
theorem rev147_plane52_mem : rev147_plane52 ∈ rev147_planes := by decide
def rev147_plane57 : IntegerPlane := ⟨(-287616000000),(-1855520000000),(-1643759759600)⟩
theorem rev147_plane57_mem : rev147_plane57 ∈ rev147_planes := by decide
def rev147_vertex0 : FractionPoint := fractionRow147[0]!
theorem rev147_vertex0_mem : rev147_vertex0∈fractionRow147 := by decide
def rev147_vertex1 : FractionPoint := fractionRow147[1]!
theorem rev147_vertex1_mem : rev147_vertex1∈fractionRow147 := by decide
def rev147_vertex2 : FractionPoint := fractionRow147[2]!
theorem rev147_vertex2_mem : rev147_vertex2∈fractionRow147 := by decide
def rev147_s0_ll : FractionPoint := ⟨16877002803328811,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev147_s0_ll_mem : rev147_s0_ll.real ∈ rationalHull (fractionRow147.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow147 rev147_plane57 rev147_vertex2 rev147_vertex0 rev147_s0_ll
    rev147_vertex2_mem rev147_vertex0_mem (by decide)
def rev147_s0_lr : FractionPoint := ⟨119631870441922553,155621401706400000,164729284083707661293,214850166141562000000⟩
theorem rev147_s0_lr_mem : rev147_s0_lr.real ∈ rationalHull (fractionRow147.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow147 rev147_plane57 rev147_vertex2 rev147_vertex0 rev147_s0_lr
    rev147_vertex2_mem rev147_vertex0_mem (by decide)
def rev147_s0_ul : FractionPoint := ⟨16877002803328811,21955087795200000,1001990771613779,1306850464000000⟩
theorem rev147_s0_ul_mem : rev147_s0_ul.real ∈ rationalHull (fractionRow147.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow147 rev147_plane52 rev147_vertex2 rev147_vertex1 rev147_s0_ul
    rev147_vertex2_mem rev147_vertex1_mem (by decide)
def rev147_s0_ur : FractionPoint := ⟨119631870441922553,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev147_s0_ur_mem : rev147_s0_ur.real ∈ rationalHull (fractionRow147.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow147 rev147_plane52 rev147_vertex2 rev147_vertex1 rev147_s0_ur
    rev147_vertex2_mem rev147_vertex1_mem (by decide)
theorem rev147_slab0 (p : Point) (hp : p∈IntegerCarrier rev147_planes)
    (hx0 : rev147_s0_ll.real.1≤p.1) (hx1 : p.1≤rev147_s0_lr.real.1) :
    p∈rationalHull (fractionRow147.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev147_plane57 rev147_plane52 rev147_s0_ll rev147_s0_lr rev147_s0_ul rev147_s0_ur
    (by decide) rev147_s0_ll_mem rev147_s0_lr_mem rev147_s0_ul_mem rev147_s0_ur_mem p
    (hp _ rev147_plane57_mem) (hp _ rev147_plane52_mem) hx0 hx1
def rev147_s1_ll : FractionPoint := ⟨119631870441922553,155621401706400000,164729284083707661293,214850166141562000000⟩
theorem rev147_s1_ll_mem : rev147_s1_ll.real ∈ rationalHull (fractionRow147.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow147 rev147_plane57 rev147_vertex2 rev147_vertex0 rev147_s1_ll
    rev147_vertex2_mem rev147_vertex0_mem (by decide)
def rev147_s1_lr : FractionPoint := ⟨8498840334319621,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev147_s1_lr_mem : rev147_s1_lr.real ∈ rationalHull (fractionRow147.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow147 rev147_plane57 rev147_vertex2 rev147_vertex0 rev147_s1_lr
    rev147_vertex2_mem rev147_vertex0_mem (by decide)
def rev147_s1_ul : FractionPoint := ⟨119631870441922553,155621401706400000,28419630852349427,37052714692000000⟩
theorem rev147_s1_ul_mem : rev147_s1_ul.real ∈ rationalHull (fractionRow147.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow147 rev147_plane19 rev147_vertex1 rev147_vertex0 rev147_s1_ul
    rev147_vertex1_mem rev147_vertex0_mem (by decide)
def rev147_s1_ur : FractionPoint := ⟨8498840334319621,11052462565200000,2017556719765051,2631538706000000⟩
theorem rev147_s1_ur_mem : rev147_s1_ur.real ∈ rationalHull (fractionRow147.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow147 rev147_plane19 rev147_vertex1 rev147_vertex0 rev147_s1_ur
    rev147_vertex1_mem rev147_vertex0_mem (by decide)
theorem rev147_slab1 (p : Point) (hp : p∈IntegerCarrier rev147_planes)
    (hx0 : rev147_s1_ll.real.1≤p.1) (hx1 : p.1≤rev147_s1_lr.real.1) :
    p∈rationalHull (fractionRow147.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev147_plane57 rev147_plane19 rev147_s1_ll rev147_s1_lr rev147_s1_ul rev147_s1_ur
    (by decide) rev147_s1_ll_mem rev147_s1_lr_mem rev147_s1_ul_mem rev147_s1_ur_mem p
    (hp _ rev147_plane57_mem) (hp _ rev147_plane19_mem) hx0 hx1
theorem rev147_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev147_planes) : rev147_s0_ll.real.1≤p.1 := by
  have hc := rev147_plane52.combine_sound rev147_plane57 1855520000000 202532000000 (by decide) (by decide) p
    (hp _ rev147_plane52_mem) (hp _ rev147_plane57_mem)
  exact (rev147_plane52.combine rev147_plane57 1855520000000 202532000000).xBoundCheck_sound rev147_s0_ll.nx rev147_s0_ll.dx true (by decide) p hc
theorem rev147_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev147_planes) : p.1≤rev147_s1_lr.real.1 := by
  have hc := rev147_plane19.combine_sound rev147_plane57 1855520000000 1440116000000 (by decide) (by decide) p
    (hp _ rev147_plane19_mem) (hp _ rev147_plane57_mem)
  exact (rev147_plane19.combine rev147_plane57 1855520000000 1440116000000).xBoundCheck_sound rev147_s1_lr.nx rev147_s1_lr.dx false (by decide) p hc
theorem rev147_hull (p : Point) (hp : p∈IntegerCarrier rev147_planes) :
    p∈rationalHull (fractionRow147.map FractionPoint.rational) := by
  have hxlo := rev147_bound0_lo p hp
  have hxhi := rev147_bound0_hi p hp
  by_cases h0 : p.1≤rev147_s0_lr.real.1
  · exact rev147_slab0 p hp hxlo h0
  exact rev147_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull147 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,8,12,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow147 := by
  rw [← fractionRow147_correct]
  exact rev147_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull147
