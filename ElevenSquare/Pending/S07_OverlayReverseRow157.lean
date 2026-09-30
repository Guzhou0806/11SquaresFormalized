import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks19
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev157_planes : List IntegerPlane := integerOverlayPlanes ![10,12,8,15]
def rev157_plane19 : IntegerPlane := ⟨2129316000000,1440116000000,2741459880216⟩
theorem rev157_plane19_mem : rev157_plane19 ∈ rev157_planes := by decide
def rev157_plane32 : IntegerPlane := ⟨202532000000,(-1861776000000),(-1275872260553)⟩
theorem rev157_plane32_mem : rev157_plane32 ∈ rev157_planes := by decide
def rev157_plane37 : IntegerPlane := ⟨(-1855520000000),(-287616000000),(-1643759759600)⟩
theorem rev157_plane37_mem : rev157_plane37 ∈ rev157_planes := by decide
def rev157_plane74 : IntegerPlane := ⟨(-1440116000000),(-2129316000000),(-2741459880216)⟩
theorem rev157_plane74_mem : rev157_plane74 ∈ rev157_planes := by decide
def rev157_vertex0 : FractionPoint := fractionRow157[0]!
theorem rev157_vertex0_mem : rev157_vertex0∈fractionRow157 := by decide
def rev157_vertex1 : FractionPoint := fractionRow157[1]!
theorem rev157_vertex1_mem : rev157_vertex1∈fractionRow157 := by decide
def rev157_vertex2 : FractionPoint := fractionRow157[2]!
theorem rev157_vertex2_mem : rev157_vertex2∈fractionRow157 := by decide
def rev157_vertex3 : FractionPoint := fractionRow157[3]!
theorem rev157_vertex3_mem : rev157_vertex3∈fractionRow157 := by decide
def rev157_s0_ll : FractionPoint := ⟨24667453203873571,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev157_s0_ll_mem : rev157_s0_ll.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane37 rev157_vertex2 rev157_vertex3 rev157_s0_ll
    rev157_vertex2_mem rev157_vertex3_mem (by decide)
def rev157_s0_lr : FractionPoint := ⟨2017556719765051,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev157_s0_lr_mem : rev157_s0_lr.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane37 rev157_vertex2 rev157_vertex3 rev157_s0_lr
    rev157_vertex2_mem rev157_vertex3_mem (by decide)
def rev157_s0_ul : FractionPoint := ⟨24667453203873571,32183417026000000,4958592752081121,6436683405200000⟩
theorem rev157_s0_ul_mem : rev157_s0_ul.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane19 rev157_vertex2 rev157_vertex1 rev157_s0_ul
    rev157_vertex2_mem rev157_vertex1_mem (by decide)
def rev157_s0_ur : FractionPoint := ⟨2017556719765051,2631538706000000,145912099071564415269,189486049756494800000⟩
theorem rev157_s0_ur_mem : rev157_s0_ur.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane19 rev157_vertex2 rev157_vertex1 rev157_s0_ur
    rev157_vertex2_mem rev157_vertex1_mem (by decide)
theorem rev157_slab0 (p : Point) (hp : p∈IntegerCarrier rev157_planes)
    (hx0 : rev157_s0_ll.real.1≤p.1) (hx1 : p.1≤rev157_s0_lr.real.1) :
    p∈rationalHull (fractionRow157.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev157_plane37 rev157_plane19 rev157_s0_ll rev157_s0_lr rev157_s0_ul rev157_s0_ur
    (by decide) rev157_s0_ll_mem rev157_s0_lr_mem rev157_s0_ul_mem rev157_s0_ur_mem p
    (hp _ rev157_plane37_mem) (hp _ rev157_plane19_mem) hx0 hx1
def rev157_s1_ll : FractionPoint := ⟨2017556719765051,2631538706000000,8498840334319621,11052462565200000⟩
theorem rev157_s1_ll_mem : rev157_s1_ll.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane74 rev157_vertex3 rev157_vertex0 rev157_s1_ll
    rev157_vertex3_mem rev157_vertex0_mem (by decide)
def rev157_s1_lr : FractionPoint := ⟨28419630852349427,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev157_s1_lr_mem : rev157_s1_lr.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane74 rev157_vertex3 rev157_vertex0 rev157_s1_lr
    rev157_vertex3_mem rev157_vertex0_mem (by decide)
def rev157_s1_ul : FractionPoint := ⟨2017556719765051,2631538706000000,145912099071564415269,189486049756494800000⟩
theorem rev157_s1_ul_mem : rev157_s1_ul.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane19 rev157_vertex2 rev157_vertex1 rev157_s1_ul
    rev157_vertex2_mem rev157_vertex1_mem (by decide)
def rev157_s1_ur : FractionPoint := ⟨28419630852349427,37052714692000000,293315400665761934511,381144337652744800000⟩
theorem rev157_s1_ur_mem : rev157_s1_ur.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane19 rev157_vertex2 rev157_vertex1 rev157_s1_ur
    rev157_vertex2_mem rev157_vertex1_mem (by decide)
theorem rev157_slab1 (p : Point) (hp : p∈IntegerCarrier rev157_planes)
    (hx0 : rev157_s1_ll.real.1≤p.1) (hx1 : p.1≤rev157_s1_lr.real.1) :
    p∈rationalHull (fractionRow157.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev157_plane74 rev157_plane19 rev157_s1_ll rev157_s1_lr rev157_s1_ul rev157_s1_ur
    (by decide) rev157_s1_ll_mem rev157_s1_lr_mem rev157_s1_ul_mem rev157_s1_ur_mem p
    (hp _ rev157_plane74_mem) (hp _ rev157_plane19_mem) hx0 hx1
def rev157_s2_ll : FractionPoint := ⟨28419630852349427,37052714692000000,119631870441922553,155621401706400000⟩
theorem rev157_s2_ll_mem : rev157_s2_ll.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane32 rev157_vertex0 rev157_vertex1 rev157_s2_ll
    rev157_vertex0_mem rev157_vertex1_mem (by decide)
def rev157_s2_lr : FractionPoint := ⟨816645038392619867,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev157_s2_lr_mem : rev157_s2_lr.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane32 rev157_vertex0 rev157_vertex1 rev157_s2_lr
    rev157_vertex0_mem rev157_vertex1_mem (by decide)
def rev157_s2_ul : FractionPoint := ⟨28419630852349427,37052714692000000,293315400665761934511,381144337652744800000⟩
theorem rev157_s2_ul_mem : rev157_s2_ul.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane19 rev157_vertex2 rev157_vertex1 rev157_s2_ul
    rev157_vertex2_mem rev157_vertex1_mem (by decide)
def rev157_s2_ur : FractionPoint := ⟨816645038392619867,1063994749732000000,163598428540578933,212798949946400000⟩
theorem rev157_s2_ur_mem : rev157_s2_ur.real ∈ rationalHull (fractionRow157.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow157 rev157_plane19 rev157_vertex2 rev157_vertex1 rev157_s2_ur
    rev157_vertex2_mem rev157_vertex1_mem (by decide)
theorem rev157_slab2 (p : Point) (hp : p∈IntegerCarrier rev157_planes)
    (hx0 : rev157_s2_ll.real.1≤p.1) (hx1 : p.1≤rev157_s2_lr.real.1) :
    p∈rationalHull (fractionRow157.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev157_plane32 rev157_plane19 rev157_s2_ll rev157_s2_lr rev157_s2_ul rev157_s2_ur
    (by decide) rev157_s2_ll_mem rev157_s2_lr_mem rev157_s2_ul_mem rev157_s2_ur_mem p
    (hp _ rev157_plane32_mem) (hp _ rev157_plane19_mem) hx0 hx1
theorem rev157_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev157_planes) : rev157_s0_ll.real.1≤p.1 := by
  have hc := rev157_plane19.combine_sound rev157_plane37 287616000000 1440116000000 (by decide) (by decide) p
    (hp _ rev157_plane19_mem) (hp _ rev157_plane37_mem)
  exact (rev157_plane19.combine rev157_plane37 287616000000 1440116000000).xBoundCheck_sound rev157_s0_ll.nx rev157_s0_ll.dx true (by decide) p hc
theorem rev157_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev157_planes) : p.1≤rev157_s2_lr.real.1 := by
  have hc := rev157_plane19.combine_sound rev157_plane32 1861776000000 1440116000000 (by decide) (by decide) p
    (hp _ rev157_plane19_mem) (hp _ rev157_plane32_mem)
  exact (rev157_plane19.combine rev157_plane32 1861776000000 1440116000000).xBoundCheck_sound rev157_s2_lr.nx rev157_s2_lr.dx false (by decide) p hc
theorem rev157_hull (p : Point) (hp : p∈IntegerCarrier rev157_planes) :
    p∈rationalHull (fractionRow157.map FractionPoint.rational) := by
  have hxlo := rev157_bound0_lo p hp
  have hxhi := rev157_bound0_hi p hp
  by_cases h0 : p.1≤rev157_s0_lr.real.1
  · exact rev157_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev157_s1_lr.real.1
  · exact rev157_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev157_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull157 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,12,8,15] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow157 := by
  rw [← fractionRow157_correct]
  exact rev157_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull157
