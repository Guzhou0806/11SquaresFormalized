import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks19
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev156_planes : List IntegerPlane := integerOverlayPlanes ![10,12,8,10]
def rev156_plane32 : IntegerPlane := ⟨202532000000,(-1861776000000),(-1275872260553)⟩
theorem rev156_plane32_mem : rev156_plane32 ∈ rev156_planes := by decide
def rev156_plane37 : IntegerPlane := ⟨(-1855520000000),(-287616000000),(-1643759759600)⟩
theorem rev156_plane37_mem : rev156_plane37 ∈ rev156_planes := by decide
def rev156_plane79 : IntegerPlane := ⟨1440116000000,2129316000000,2741459880216⟩
theorem rev156_plane79_mem : rev156_plane79 ∈ rev156_planes := by decide
def rev156_vertex0 : FractionPoint := fractionRow156[0]!
theorem rev156_vertex0_mem : rev156_vertex0∈fractionRow156 := by decide
def rev156_vertex1 : FractionPoint := fractionRow156[1]!
theorem rev156_vertex1_mem : rev156_vertex1∈fractionRow156 := by decide
def rev156_vertex2 : FractionPoint := fractionRow156[2]!
theorem rev156_vertex2_mem : rev156_vertex2∈fractionRow156 := by decide
def rev156_s0_ll : FractionPoint := ⟨2017556719765051,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev156_s0_ll_mem : rev156_s0_ll.real ∈ rationalHull (fractionRow156.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow156 rev156_plane37 rev156_vertex2 rev156_vertex0 rev156_s0_ll
    rev156_vertex2_mem rev156_vertex0_mem (by decide)
def rev156_s0_lr : FractionPoint := ⟨1001990771613779,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev156_s0_lr_mem : rev156_s0_lr.real ∈ rationalHull (fractionRow156.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow156 rev156_plane37 rev156_vertex2 rev156_vertex0 rev156_s0_lr
    rev156_vertex2_mem rev156_vertex0_mem (by decide)
def rev156_s0_ul : FractionPoint := ⟨2017556719765051,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev156_s0_ul_mem : rev156_s0_ul.real ∈ rationalHull (fractionRow156.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow156 rev156_plane79 rev156_vertex2 rev156_vertex1 rev156_s0_ul
    rev156_vertex2_mem rev156_vertex1_mem (by decide)
def rev156_s0_ur : FractionPoint := ⟨1001990771613779,1306850464000000,106984758722215753093,139134880130131200000⟩
theorem rev156_s0_ur_mem : rev156_s0_ur.real ∈ rationalHull (fractionRow156.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow156 rev156_plane79 rev156_vertex2 rev156_vertex1 rev156_s0_ur
    rev156_vertex2_mem rev156_vertex1_mem (by decide)
theorem rev156_slab0 (p : Point) (hp : p∈IntegerCarrier rev156_planes)
    (hx0 : rev156_s0_ll.real.1≤p.1) (hx1 : p.1≤rev156_s0_lr.real.1) :
    p∈rationalHull (fractionRow156.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev156_plane37 rev156_plane79 rev156_s0_ll rev156_s0_lr rev156_s0_ul rev156_s0_ur
    (by decide) rev156_s0_ll_mem rev156_s0_lr_mem rev156_s0_ul_mem rev156_s0_ur_mem p
    (hp _ rev156_plane37_mem) (hp _ rev156_plane79_mem) hx0 hx1
def rev156_s1_ll : FractionPoint := ⟨1001990771613779,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev156_s1_ll_mem : rev156_s1_ll.real ∈ rationalHull (fractionRow156.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow156 rev156_plane32 rev156_vertex0 rev156_vertex1 rev156_s1_ll
    rev156_vertex0_mem rev156_vertex1_mem (by decide)
def rev156_s1_lr : FractionPoint := ⟨28419630852349427,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev156_s1_lr_mem : rev156_s1_lr.real ∈ rationalHull (fractionRow156.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow156 rev156_plane32 rev156_vertex0 rev156_vertex1 rev156_s1_lr
    rev156_vertex0_mem rev156_vertex1_mem (by decide)
def rev156_s1_ul : FractionPoint := ⟨1001990771613779,1306850464000000,106984758722215753093,139134880130131200000⟩
theorem rev156_s1_ul_mem : rev156_s1_ul.real ∈ rationalHull (fractionRow156.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow156 rev156_plane79 rev156_vertex2 rev156_vertex1 rev156_s1_ul
    rev156_vertex2_mem rev156_vertex1_mem (by decide)
def rev156_s1_ur : FractionPoint := ⟨28419630852349427,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev156_s1_ur_mem : rev156_s1_ur.real ∈ rationalHull (fractionRow156.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow156 rev156_plane79 rev156_vertex2 rev156_vertex1 rev156_s1_ur
    rev156_vertex2_mem rev156_vertex1_mem (by decide)
theorem rev156_slab1 (p : Point) (hp : p∈IntegerCarrier rev156_planes)
    (hx0 : rev156_s1_ll.real.1≤p.1) (hx1 : p.1≤rev156_s1_lr.real.1) :
    p∈rationalHull (fractionRow156.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev156_plane32 rev156_plane79 rev156_s1_ll rev156_s1_lr rev156_s1_ul rev156_s1_ur
    (by decide) rev156_s1_ll_mem rev156_s1_lr_mem rev156_s1_ul_mem rev156_s1_ur_mem p
    (hp _ rev156_plane32_mem) (hp _ rev156_plane79_mem) hx0 hx1
theorem rev156_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev156_planes) : rev156_s0_ll.real.1≤p.1 := by
  have hc := rev156_plane37.combine_sound rev156_plane79 2129316000000 287616000000 (by decide) (by decide) p
    (hp _ rev156_plane37_mem) (hp _ rev156_plane79_mem)
  exact (rev156_plane37.combine rev156_plane79 2129316000000 287616000000).xBoundCheck_sound rev156_s0_ll.nx rev156_s0_ll.dx true (by decide) p hc
theorem rev156_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev156_planes) : p.1≤rev156_s1_lr.real.1 := by
  have hc := rev156_plane32.combine_sound rev156_plane79 2129316000000 1861776000000 (by decide) (by decide) p
    (hp _ rev156_plane32_mem) (hp _ rev156_plane79_mem)
  exact (rev156_plane32.combine rev156_plane79 2129316000000 1861776000000).xBoundCheck_sound rev156_s1_lr.nx rev156_s1_lr.dx false (by decide) p hc
theorem rev156_hull (p : Point) (hp : p∈IntegerCarrier rev156_planes) :
    p∈rationalHull (fractionRow156.map FractionPoint.rational) := by
  have hxlo := rev156_bound0_lo p hp
  have hxhi := rev156_bound0_hi p hp
  by_cases h0 : p.1≤rev156_s0_lr.real.1
  · exact rev156_slab0 p hp hxlo h0
  exact rev156_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull156 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,12,8,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow156 := by
  rw [← fractionRow156_correct]
  exact rev156_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull156
