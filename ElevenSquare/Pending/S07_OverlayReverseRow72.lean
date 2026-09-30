import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks9
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev72_planes : List IntegerPlane := integerOverlayPlanes ![5,7,3,5]
def rev72_plane4 : IntegerPlane := ⟨(-2129316000000),(-1440116000000),(-827972119784)⟩
theorem rev72_plane4_mem : rev72_plane4 ∈ rev72_planes := by decide
def rev72_plane46 : IntegerPlane := ⟨287616000000,1855520000000,499376240400⟩
theorem rev72_plane46_mem : rev72_plane46 ∈ rev72_planes := by decide
def rev72_plane51 : IntegerPlane := ⟨1861776000000,(-202532000000),383371739447⟩
theorem rev72_plane51_mem : rev72_plane51 ∈ rev72_planes := by decide
def rev72_vertex0 : FractionPoint := fractionRow72[0]!
theorem rev72_vertex0_mem : rev72_vertex0∈fractionRow72 := by decide
def rev72_vertex1 : FractionPoint := fractionRow72[1]!
theorem rev72_vertex1_mem : rev72_vertex1∈fractionRow72 := by decide
def rev72_vertex2 : FractionPoint := fractionRow72[2]!
theorem rev72_vertex2_mem : rev72_vertex2∈fractionRow72 := by decide
def rev72_s0_ll : FractionPoint := ⟨2553622230880379,11052462565200000,613981986234949,2631538706000000⟩
theorem rev72_s0_ll_mem : rev72_s0_ll.real ∈ rationalHull (fractionRow72.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow72 rev72_plane4 rev72_vertex0 rev72_vertex1 rev72_s0_ll
    rev72_vertex0_mem rev72_vertex1_mem (by decide)
def rev72_s0_lr : FractionPoint := ⟨35989531264477447,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev72_s0_lr_mem : rev72_s0_lr.real ∈ rationalHull (fractionRow72.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow72 rev72_plane4 rev72_vertex0 rev72_vertex1 rev72_s0_lr
    rev72_vertex0_mem rev72_vertex1_mem (by decide)
def rev72_s0_ul : FractionPoint := ⟨2553622230880379,11052462565200000,613981986234949,2631538706000000⟩
theorem rev72_s0_ul_mem : rev72_s0_ul.real ∈ rationalHull (fractionRow72.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow72 rev72_plane46 rev72_vertex0 rev72_vertex2 rev72_s0_ul
    rev72_vertex0_mem rev72_vertex2_mem (by decide)
def rev72_s0_ur : FractionPoint := ⟨35989531264477447,155621401706400000,50120882057854338707,214850166141562000000⟩
theorem rev72_s0_ur_mem : rev72_s0_ur.real ∈ rationalHull (fractionRow72.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow72 rev72_plane46 rev72_vertex0 rev72_vertex2 rev72_s0_ur
    rev72_vertex0_mem rev72_vertex2_mem (by decide)
theorem rev72_slab0 (p : Point) (hp : p∈IntegerCarrier rev72_planes)
    (hx0 : rev72_s0_ll.real.1≤p.1) (hx1 : p.1≤rev72_s0_lr.real.1) :
    p∈rationalHull (fractionRow72.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev72_plane4 rev72_plane46 rev72_s0_ll rev72_s0_lr rev72_s0_ul rev72_s0_ur
    (by decide) rev72_s0_ll_mem rev72_s0_lr_mem rev72_s0_ul_mem rev72_s0_ur_mem p
    (hp _ rev72_plane4_mem) (hp _ rev72_plane46_mem) hx0 hx1
def rev72_s1_ll : FractionPoint := ⟨35989531264477447,155621401706400000,8633083839650573,37052714692000000⟩
theorem rev72_s1_ll_mem : rev72_s1_ll.real ∈ rationalHull (fractionRow72.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow72 rev72_plane51 rev72_vertex1 rev72_vertex2 rev72_s1_ll
    rev72_vertex1_mem rev72_vertex2_mem (by decide)
def rev72_s1_lr : FractionPoint := ⟨5078084991871189,21955087795200000,304859692386221,1306850464000000⟩
theorem rev72_s1_lr_mem : rev72_s1_lr.real ∈ rationalHull (fractionRow72.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow72 rev72_plane51 rev72_vertex1 rev72_vertex2 rev72_s1_lr
    rev72_vertex1_mem rev72_vertex2_mem (by decide)
def rev72_s1_ul : FractionPoint := ⟨35989531264477447,155621401706400000,50120882057854338707,214850166141562000000⟩
theorem rev72_s1_ul_mem : rev72_s1_ul.real ∈ rationalHull (fractionRow72.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow72 rev72_plane46 rev72_vertex0 rev72_vertex2 rev72_s1_ul
    rev72_vertex0_mem rev72_vertex2_mem (by decide)
def rev72_s1_ur : FractionPoint := ⟨5078084991871189,21955087795200000,304859692386221,1306850464000000⟩
theorem rev72_s1_ur_mem : rev72_s1_ur.real ∈ rationalHull (fractionRow72.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow72 rev72_plane46 rev72_vertex0 rev72_vertex2 rev72_s1_ur
    rev72_vertex0_mem rev72_vertex2_mem (by decide)
theorem rev72_slab1 (p : Point) (hp : p∈IntegerCarrier rev72_planes)
    (hx0 : rev72_s1_ll.real.1≤p.1) (hx1 : p.1≤rev72_s1_lr.real.1) :
    p∈rationalHull (fractionRow72.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev72_plane51 rev72_plane46 rev72_s1_ll rev72_s1_lr rev72_s1_ul rev72_s1_ur
    (by decide) rev72_s1_ll_mem rev72_s1_lr_mem rev72_s1_ul_mem rev72_s1_ur_mem p
    (hp _ rev72_plane51_mem) (hp _ rev72_plane46_mem) hx0 hx1
theorem rev72_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev72_planes) : rev72_s0_ll.real.1≤p.1 := by
  have hc := rev72_plane4.combine_sound rev72_plane46 1855520000000 1440116000000 (by decide) (by decide) p
    (hp _ rev72_plane4_mem) (hp _ rev72_plane46_mem)
  exact (rev72_plane4.combine rev72_plane46 1855520000000 1440116000000).xBoundCheck_sound rev72_s0_ll.nx rev72_s0_ll.dx true (by decide) p hc
theorem rev72_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev72_planes) : p.1≤rev72_s1_lr.real.1 := by
  have hc := rev72_plane46.combine_sound rev72_plane51 202532000000 1855520000000 (by decide) (by decide) p
    (hp _ rev72_plane46_mem) (hp _ rev72_plane51_mem)
  exact (rev72_plane46.combine rev72_plane51 202532000000 1855520000000).xBoundCheck_sound rev72_s1_lr.nx rev72_s1_lr.dx false (by decide) p hc
theorem rev72_hull (p : Point) (hp : p∈IntegerCarrier rev72_planes) :
    p∈rationalHull (fractionRow72.map FractionPoint.rational) := by
  have hxlo := rev72_bound0_lo p hp
  have hxhi := rev72_bound0_hi p hp
  by_cases h0 : p.1≤rev72_s0_lr.real.1
  · exact rev72_slab0 p hp hxlo h0
  exact rev72_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull72 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,7,3,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow72 := by
  rw [← fractionRow72_correct]
  exact rev72_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull72
