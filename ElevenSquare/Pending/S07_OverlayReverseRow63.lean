import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks7
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev63_planes : List IntegerPlane := integerOverlayPlanes ![5,3,7,5]
def rev63_plane26 : IntegerPlane := ⟨1855520000000,287616000000,499376240400⟩
theorem rev63_plane26_mem : rev63_plane26 ∈ rev63_planes := by decide
def rev63_plane31 : IntegerPlane := ⟨(-202532000000),1861776000000,383371739447⟩
theorem rev63_plane31_mem : rev63_plane31 ∈ rev63_planes := by decide
def rev63_plane64 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-827972119784)⟩
theorem rev63_plane64_mem : rev63_plane64 ∈ rev63_planes := by decide
def rev63_vertex0 : FractionPoint := fractionRow63[0]!
theorem rev63_vertex0_mem : rev63_vertex0∈fractionRow63 := by decide
def rev63_vertex1 : FractionPoint := fractionRow63[1]!
theorem rev63_vertex1_mem : rev63_vertex1∈fractionRow63 := by decide
def rev63_vertex2 : FractionPoint := fractionRow63[2]!
theorem rev63_vertex2_mem : rev63_vertex2∈fractionRow63 := by decide
def rev63_s0_ll : FractionPoint := ⟨8633083839650573,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev63_s0_ll_mem : rev63_s0_ll.real ∈ rationalHull (fractionRow63.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow63 rev63_plane64 rev63_vertex2 rev63_vertex0 rev63_s0_ll
    rev63_vertex2_mem rev63_vertex0_mem (by decide)
def rev63_s0_lr : FractionPoint := ⟨304859692386221,1306850464000000,32150121407915446907,139134880130131200000⟩
theorem rev63_s0_lr_mem : rev63_s0_lr.real ∈ rationalHull (fractionRow63.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow63 rev63_plane64 rev63_vertex2 rev63_vertex0 rev63_s0_lr
    rev63_vertex2_mem rev63_vertex0_mem (by decide)
def rev63_s0_ul : FractionPoint := ⟨8633083839650573,37052714692000000,35989531264477447,155621401706400000⟩
theorem rev63_s0_ul_mem : rev63_s0_ul.real ∈ rationalHull (fractionRow63.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow63 rev63_plane31 rev63_vertex2 rev63_vertex1 rev63_s0_ul
    rev63_vertex2_mem rev63_vertex1_mem (by decide)
def rev63_s0_ur : FractionPoint := ⟨304859692386221,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev63_s0_ur_mem : rev63_s0_ur.real ∈ rationalHull (fractionRow63.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow63 rev63_plane31 rev63_vertex2 rev63_vertex1 rev63_s0_ur
    rev63_vertex2_mem rev63_vertex1_mem (by decide)
theorem rev63_slab0 (p : Point) (hp : p∈IntegerCarrier rev63_planes)
    (hx0 : rev63_s0_ll.real.1≤p.1) (hx1 : p.1≤rev63_s0_lr.real.1) :
    p∈rationalHull (fractionRow63.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev63_plane64 rev63_plane31 rev63_s0_ll rev63_s0_lr rev63_s0_ul rev63_s0_ur
    (by decide) rev63_s0_ll_mem rev63_s0_lr_mem rev63_s0_ul_mem rev63_s0_ur_mem p
    (hp _ rev63_plane64_mem) (hp _ rev63_plane31_mem) hx0 hx1
def rev63_s1_ll : FractionPoint := ⟨304859692386221,1306850464000000,32150121407915446907,139134880130131200000⟩
theorem rev63_s1_ll_mem : rev63_s1_ll.real ∈ rationalHull (fractionRow63.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow63 rev63_plane64 rev63_vertex2 rev63_vertex0 rev63_s1_ll
    rev63_vertex2_mem rev63_vertex0_mem (by decide)
def rev63_s1_lr : FractionPoint := ⟨613981986234949,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev63_s1_lr_mem : rev63_s1_lr.real ∈ rationalHull (fractionRow63.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow63 rev63_plane64 rev63_vertex2 rev63_vertex0 rev63_s1_lr
    rev63_vertex2_mem rev63_vertex0_mem (by decide)
def rev63_s1_ul : FractionPoint := ⟨304859692386221,1306850464000000,5078084991871189,21955087795200000⟩
theorem rev63_s1_ul_mem : rev63_s1_ul.real ∈ rationalHull (fractionRow63.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow63 rev63_plane26 rev63_vertex1 rev63_vertex0 rev63_s1_ul
    rev63_vertex1_mem rev63_vertex0_mem (by decide)
def rev63_s1_ur : FractionPoint := ⟨613981986234949,2631538706000000,2553622230880379,11052462565200000⟩
theorem rev63_s1_ur_mem : rev63_s1_ur.real ∈ rationalHull (fractionRow63.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow63 rev63_plane26 rev63_vertex1 rev63_vertex0 rev63_s1_ur
    rev63_vertex1_mem rev63_vertex0_mem (by decide)
theorem rev63_slab1 (p : Point) (hp : p∈IntegerCarrier rev63_planes)
    (hx0 : rev63_s1_ll.real.1≤p.1) (hx1 : p.1≤rev63_s1_lr.real.1) :
    p∈rationalHull (fractionRow63.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev63_plane64 rev63_plane26 rev63_s1_ll rev63_s1_lr rev63_s1_ul rev63_s1_ur
    (by decide) rev63_s1_ll_mem rev63_s1_lr_mem rev63_s1_ul_mem rev63_s1_ur_mem p
    (hp _ rev63_plane64_mem) (hp _ rev63_plane26_mem) hx0 hx1
theorem rev63_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev63_planes) : rev63_s0_ll.real.1≤p.1 := by
  have hc := rev63_plane31.combine_sound rev63_plane64 2129316000000 1861776000000 (by decide) (by decide) p
    (hp _ rev63_plane31_mem) (hp _ rev63_plane64_mem)
  exact (rev63_plane31.combine rev63_plane64 2129316000000 1861776000000).xBoundCheck_sound rev63_s0_ll.nx rev63_s0_ll.dx true (by decide) p hc
theorem rev63_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev63_planes) : p.1≤rev63_s1_lr.real.1 := by
  have hc := rev63_plane26.combine_sound rev63_plane64 2129316000000 287616000000 (by decide) (by decide) p
    (hp _ rev63_plane26_mem) (hp _ rev63_plane64_mem)
  exact (rev63_plane26.combine rev63_plane64 2129316000000 287616000000).xBoundCheck_sound rev63_s1_lr.nx rev63_s1_lr.dx false (by decide) p hc
theorem rev63_hull (p : Point) (hp : p∈IntegerCarrier rev63_planes) :
    p∈rationalHull (fractionRow63.map FractionPoint.rational) := by
  have hxlo := rev63_bound0_lo p hp
  have hxhi := rev63_bound0_hi p hp
  by_cases h0 : p.1≤rev63_s0_lr.real.1
  · exact rev63_slab0 p hp hxlo h0
  exact rev63_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull63 (p : Point)
    (hp : ∀ g, ClosedCell ((![5,3,7,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow63 := by
  rw [← fractionRow63_correct]
  exact rev63_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull63
