import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks13
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev107_planes : List IntegerPlane := integerOverlayPlanes ![7,5,10,12]
def rev107_plane24 : IntegerPlane := ⟨2129316000000,(-1440116000000),1301343880216⟩
theorem rev107_plane24_mem : rev107_plane24 ∈ rev107_planes := by decide
def rev107_plane72 : IntegerPlane := ⟨(-1861776000000),(-202532000000),(-1478404260553)⟩
theorem rev107_plane72_mem : rev107_plane72 ∈ rev107_planes := by decide
def rev107_plane77 : IntegerPlane := ⟨(-287616000000),1855520000000,211760240400⟩
theorem rev107_plane77_mem : rev107_plane77 ∈ rev107_planes := by decide
def rev107_vertex0 : FractionPoint := fractionRow107[0]!
theorem rev107_vertex0_mem : rev107_vertex0∈fractionRow107 := by decide
def rev107_vertex1 : FractionPoint := fractionRow107[1]!
theorem rev107_vertex1_mem : rev107_vertex1∈fractionRow107 := by decide
def rev107_vertex2 : FractionPoint := fractionRow107[2]!
theorem rev107_vertex2_mem : rev107_vertex2∈fractionRow107 := by decide
def rev107_s0_ll : FractionPoint := ⟨16877002803328811,21955087795200000,304859692386221,1306850464000000⟩
theorem rev107_s0_ll_mem : rev107_s0_ll.real ∈ rationalHull (fractionRow107.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow107 rev107_plane72 rev107_vertex0 rev107_vertex1 rev107_s0_ll
    rev107_vertex0_mem rev107_vertex1_mem (by decide)
def rev107_s0_lr : FractionPoint := ⟨119631870441922553,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev107_s0_lr_mem : rev107_s0_lr.real ∈ rationalHull (fractionRow107.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow107 rev107_plane72 rev107_vertex0 rev107_vertex1 rev107_s0_lr
    rev107_vertex0_mem rev107_vertex1_mem (by decide)
def rev107_s0_ul : FractionPoint := ⟨16877002803328811,21955087795200000,304859692386221,1306850464000000⟩
theorem rev107_s0_ul_mem : rev107_s0_ul.real ∈ rationalHull (fractionRow107.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow107 rev107_plane77 rev107_vertex0 rev107_vertex2 rev107_s0_ul
    rev107_vertex0_mem rev107_vertex2_mem (by decide)
def rev107_s0_ur : FractionPoint := ⟨119631870441922553,155621401706400000,50120882057854338707,214850166141562000000⟩
theorem rev107_s0_ur_mem : rev107_s0_ur.real ∈ rationalHull (fractionRow107.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow107 rev107_plane77 rev107_vertex0 rev107_vertex2 rev107_s0_ur
    rev107_vertex0_mem rev107_vertex2_mem (by decide)
theorem rev107_slab0 (p : Point) (hp : p∈IntegerCarrier rev107_planes)
    (hx0 : rev107_s0_ll.real.1≤p.1) (hx1 : p.1≤rev107_s0_lr.real.1) :
    p∈rationalHull (fractionRow107.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev107_plane72 rev107_plane77 rev107_s0_ll rev107_s0_lr rev107_s0_ul rev107_s0_ur
    (by decide) rev107_s0_ll_mem rev107_s0_lr_mem rev107_s0_ul_mem rev107_s0_ur_mem p
    (hp _ rev107_plane72_mem) (hp _ rev107_plane77_mem) hx0 hx1
def rev107_s1_ll : FractionPoint := ⟨119631870441922553,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev107_s1_ll_mem : rev107_s1_ll.real ∈ rationalHull (fractionRow107.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow107 rev107_plane24 rev107_vertex1 rev107_vertex2 rev107_s1_ll
    rev107_vertex1_mem rev107_vertex2_mem (by decide)
def rev107_s1_lr : FractionPoint := ⟨8498840334319621,11052462565200000,613981986234949,2631538706000000⟩
theorem rev107_s1_lr_mem : rev107_s1_lr.real ∈ rationalHull (fractionRow107.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow107 rev107_plane24 rev107_vertex1 rev107_vertex2 rev107_s1_lr
    rev107_vertex1_mem rev107_vertex2_mem (by decide)
def rev107_s1_ul : FractionPoint := ⟨119631870441922553,155621401706400000,50120882057854338707,214850166141562000000⟩
theorem rev107_s1_ul_mem : rev107_s1_ul.real ∈ rationalHull (fractionRow107.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow107 rev107_plane77 rev107_vertex0 rev107_vertex2 rev107_s1_ul
    rev107_vertex0_mem rev107_vertex2_mem (by decide)
def rev107_s1_ur : FractionPoint := ⟨8498840334319621,11052462565200000,613981986234949,2631538706000000⟩
theorem rev107_s1_ur_mem : rev107_s1_ur.real ∈ rationalHull (fractionRow107.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow107 rev107_plane77 rev107_vertex0 rev107_vertex2 rev107_s1_ur
    rev107_vertex0_mem rev107_vertex2_mem (by decide)
theorem rev107_slab1 (p : Point) (hp : p∈IntegerCarrier rev107_planes)
    (hx0 : rev107_s1_ll.real.1≤p.1) (hx1 : p.1≤rev107_s1_lr.real.1) :
    p∈rationalHull (fractionRow107.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev107_plane24 rev107_plane77 rev107_s1_ll rev107_s1_lr rev107_s1_ul rev107_s1_ur
    (by decide) rev107_s1_ll_mem rev107_s1_lr_mem rev107_s1_ul_mem rev107_s1_ur_mem p
    (hp _ rev107_plane24_mem) (hp _ rev107_plane77_mem) hx0 hx1
theorem rev107_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev107_planes) : rev107_s0_ll.real.1≤p.1 := by
  have hc := rev107_plane72.combine_sound rev107_plane77 1855520000000 202532000000 (by decide) (by decide) p
    (hp _ rev107_plane72_mem) (hp _ rev107_plane77_mem)
  exact (rev107_plane72.combine rev107_plane77 1855520000000 202532000000).xBoundCheck_sound rev107_s0_ll.nx rev107_s0_ll.dx true (by decide) p hc
theorem rev107_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev107_planes) : p.1≤rev107_s1_lr.real.1 := by
  have hc := rev107_plane24.combine_sound rev107_plane77 1855520000000 1440116000000 (by decide) (by decide) p
    (hp _ rev107_plane24_mem) (hp _ rev107_plane77_mem)
  exact (rev107_plane24.combine rev107_plane77 1855520000000 1440116000000).xBoundCheck_sound rev107_s1_lr.nx rev107_s1_lr.dx false (by decide) p hc
theorem rev107_hull (p : Point) (hp : p∈IntegerCarrier rev107_planes) :
    p∈rationalHull (fractionRow107.map FractionPoint.rational) := by
  have hxlo := rev107_bound0_lo p hp
  have hxhi := rev107_bound0_hi p hp
  by_cases h0 : p.1≤rev107_s0_lr.real.1
  · exact rev107_slab0 p hp hxlo h0
  exact rev107_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull107 (p : Point)
    (hp : ∀ g, ClosedCell ((![7,5,10,12] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow107 := by
  rw [← fractionRow107_correct]
  exact rev107_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull107
