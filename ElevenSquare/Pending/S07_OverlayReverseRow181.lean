import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks22
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev181_planes : List IntegerPlane := integerOverlayPlanes ![12,10,5,7]
def rev181_plane12 : IntegerPlane := ⟨(-202532000000),(-1861776000000),(-1478404260553)⟩
theorem rev181_plane12_mem : rev181_plane12 ∈ rev181_planes := by decide
def rev181_plane17 : IntegerPlane := ⟨1855520000000,(-287616000000),211760240400⟩
theorem rev181_plane17_mem : rev181_plane17 ∈ rev181_planes := by decide
def rev181_plane44 : IntegerPlane := ⟨(-1440116000000),2129316000000,1301343880216⟩
theorem rev181_plane44_mem : rev181_plane44 ∈ rev181_planes := by decide
def rev181_vertex0 : FractionPoint := fractionRow181[0]!
theorem rev181_vertex0_mem : rev181_vertex0∈fractionRow181 := by decide
def rev181_vertex1 : FractionPoint := fractionRow181[1]!
theorem rev181_vertex1_mem : rev181_vertex1∈fractionRow181 := by decide
def rev181_vertex2 : FractionPoint := fractionRow181[2]!
theorem rev181_vertex2_mem : rev181_vertex2∈fractionRow181 := by decide
def rev181_s0_ll : FractionPoint := ⟨8633083839650573,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev181_s0_ll_mem : rev181_s0_ll.real ∈ rationalHull (fractionRow181.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow181 rev181_plane12 rev181_vertex0 rev181_vertex1 rev181_s0_ll
    rev181_vertex0_mem rev181_vertex1_mem (by decide)
def rev181_s0_lr : FractionPoint := ⟨304859692386221,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev181_s0_lr_mem : rev181_s0_lr.real ∈ rationalHull (fractionRow181.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow181 rev181_plane12 rev181_vertex0 rev181_vertex1 rev181_s0_lr
    rev181_vertex0_mem rev181_vertex1_mem (by decide)
def rev181_s0_ul : FractionPoint := ⟨8633083839650573,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev181_s0_ul_mem : rev181_s0_ul.real ∈ rationalHull (fractionRow181.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow181 rev181_plane44 rev181_vertex0 rev181_vertex2 rev181_s0_ul
    rev181_vertex0_mem rev181_vertex2_mem (by decide)
def rev181_s0_ur : FractionPoint := ⟨304859692386221,1306850464000000,106984758722215753093,139134880130131200000⟩
theorem rev181_s0_ur_mem : rev181_s0_ur.real ∈ rationalHull (fractionRow181.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow181 rev181_plane44 rev181_vertex0 rev181_vertex2 rev181_s0_ur
    rev181_vertex0_mem rev181_vertex2_mem (by decide)
theorem rev181_slab0 (p : Point) (hp : p∈IntegerCarrier rev181_planes)
    (hx0 : rev181_s0_ll.real.1≤p.1) (hx1 : p.1≤rev181_s0_lr.real.1) :
    p∈rationalHull (fractionRow181.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev181_plane12 rev181_plane44 rev181_s0_ll rev181_s0_lr rev181_s0_ul rev181_s0_ur
    (by decide) rev181_s0_ll_mem rev181_s0_lr_mem rev181_s0_ul_mem rev181_s0_ur_mem p
    (hp _ rev181_plane12_mem) (hp _ rev181_plane44_mem) hx0 hx1
def rev181_s1_ll : FractionPoint := ⟨304859692386221,1306850464000000,16877002803328811,21955087795200000⟩
theorem rev181_s1_ll_mem : rev181_s1_ll.real ∈ rationalHull (fractionRow181.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow181 rev181_plane17 rev181_vertex1 rev181_vertex2 rev181_s1_ll
    rev181_vertex1_mem rev181_vertex2_mem (by decide)
def rev181_s1_lr : FractionPoint := ⟨613981986234949,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev181_s1_lr_mem : rev181_s1_lr.real ∈ rationalHull (fractionRow181.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow181 rev181_plane17 rev181_vertex1 rev181_vertex2 rev181_s1_lr
    rev181_vertex1_mem rev181_vertex2_mem (by decide)
def rev181_s1_ul : FractionPoint := ⟨304859692386221,1306850464000000,106984758722215753093,139134880130131200000⟩
theorem rev181_s1_ul_mem : rev181_s1_ul.real ∈ rationalHull (fractionRow181.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow181 rev181_plane44 rev181_vertex0 rev181_vertex2 rev181_s1_ul
    rev181_vertex0_mem rev181_vertex2_mem (by decide)
def rev181_s1_ur : FractionPoint := ⟨613981986234949,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev181_s1_ur_mem : rev181_s1_ur.real ∈ rationalHull (fractionRow181.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow181 rev181_plane44 rev181_vertex0 rev181_vertex2 rev181_s1_ur
    rev181_vertex0_mem rev181_vertex2_mem (by decide)
theorem rev181_slab1 (p : Point) (hp : p∈IntegerCarrier rev181_planes)
    (hx0 : rev181_s1_ll.real.1≤p.1) (hx1 : p.1≤rev181_s1_lr.real.1) :
    p∈rationalHull (fractionRow181.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev181_plane17 rev181_plane44 rev181_s1_ll rev181_s1_lr rev181_s1_ul rev181_s1_ur
    (by decide) rev181_s1_ll_mem rev181_s1_lr_mem rev181_s1_ul_mem rev181_s1_ur_mem p
    (hp _ rev181_plane17_mem) (hp _ rev181_plane44_mem) hx0 hx1
theorem rev181_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev181_planes) : rev181_s0_ll.real.1≤p.1 := by
  have hc := rev181_plane12.combine_sound rev181_plane44 2129316000000 1861776000000 (by decide) (by decide) p
    (hp _ rev181_plane12_mem) (hp _ rev181_plane44_mem)
  exact (rev181_plane12.combine rev181_plane44 2129316000000 1861776000000).xBoundCheck_sound rev181_s0_ll.nx rev181_s0_ll.dx true (by decide) p hc
theorem rev181_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev181_planes) : p.1≤rev181_s1_lr.real.1 := by
  have hc := rev181_plane17.combine_sound rev181_plane44 2129316000000 287616000000 (by decide) (by decide) p
    (hp _ rev181_plane17_mem) (hp _ rev181_plane44_mem)
  exact (rev181_plane17.combine rev181_plane44 2129316000000 287616000000).xBoundCheck_sound rev181_s1_lr.nx rev181_s1_lr.dx false (by decide) p hc
theorem rev181_hull (p : Point) (hp : p∈IntegerCarrier rev181_planes) :
    p∈rationalHull (fractionRow181.map FractionPoint.rational) := by
  have hxlo := rev181_bound0_lo p hp
  have hxhi := rev181_bound0_hi p hp
  by_cases h0 : p.1≤rev181_s0_lr.real.1
  · exact rev181_slab0 p hp hxlo h0
  exact rev181_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull181 (p : Point)
    (hp : ∀ g, ClosedCell ((![12,10,5,7] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow181 := by
  rw [← fractionRow181_correct]
  exact rev181_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull181
