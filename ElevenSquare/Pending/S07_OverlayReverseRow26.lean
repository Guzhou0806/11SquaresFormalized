import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks3
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev26_planes : List IntegerPlane := integerOverlayPlanes ![2,5,6,9]
def rev26_plane9 : IntegerPlane := ⟨(-2099728000000),1393416000000,(-740183860516)⟩
theorem rev26_plane9_mem : rev26_plane9 ∈ rev26_planes := by decide
def rev26_plane10 : IntegerPlane := ⟨13084000000,2218132000000,623586975028⟩
theorem rev26_plane10_mem : rev26_plane10 ∈ rev26_planes := by decide
def rev26_plane54 : IntegerPlane := ⟨2168356000000,51300000000,1214821164456⟩
theorem rev26_plane54_mem : rev26_plane54 ∈ rev26_planes := by decide
def rev26_plane55 : IntegerPlane := ⟨1468788000000,(-2093220000000),256243273104⟩
theorem rev26_plane55_mem : rev26_plane55 ∈ rev26_planes := by decide
def rev26_vertex0 : FractionPoint := fractionRow26[0]!
theorem rev26_vertex0_mem : rev26_vertex0∈fractionRow26 := by decide
def rev26_vertex1 : FractionPoint := fractionRow26[1]!
theorem rev26_vertex1_mem : rev26_vertex1∈fractionRow26 := by decide
def rev26_vertex2 : FractionPoint := fractionRow26[2]!
theorem rev26_vertex2_mem : rev26_vertex2∈fractionRow26 := by decide
def rev26_vertex3 : FractionPoint := fractionRow26[3]!
theorem rev26_vertex3_mem : rev26_vertex3∈fractionRow26 := by decide
def rev26_s0_ll : FractionPoint := ⟨8279959610234849,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev26_s0_ll_mem : rev26_s0_ll.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane55 rev26_vertex2 rev26_vertex3 rev26_s0_ll
    rev26_vertex2_mem rev26_vertex3_mem (by decide)
def rev26_s0_lr : FractionPoint := ⟨31384269691121147,58446316538000000,2593363605042740122157,10195083225306030000000⟩
theorem rev26_s0_lr_mem : rev26_s0_lr.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane55 rev26_vertex2 rev26_vertex3 rev26_s0_lr
    rev26_vertex2_mem rev26_vertex3_mem (by decide)
def rev26_s0_ul : FractionPoint := ⟨8279959610234849,16309444058000000,11440249932738727,48928332174000000⟩
theorem rev26_s0_ul_mem : rev26_s0_ul.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane9 rev26_vertex2 rev26_vertex1 rev26_s0_ul
    rev26_vertex2_mem rev26_vertex1_mem (by decide)
def rev26_s0_ur : FractionPoint := ⟨31384269691121147,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev26_s0_ur_mem : rev26_s0_ur.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane9 rev26_vertex2 rev26_vertex1 rev26_s0_ur
    rev26_vertex2_mem rev26_vertex1_mem (by decide)
theorem rev26_slab0 (p : Point) (hp : p∈IntegerCarrier rev26_planes)
    (hx0 : rev26_s0_ll.real.1≤p.1) (hx1 : p.1≤rev26_s0_lr.real.1) :
    p∈rationalHull (fractionRow26.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev26_plane55 rev26_plane9 rev26_s0_ll rev26_s0_lr rev26_s0_ul rev26_s0_ur
    (by decide) rev26_s0_ll_mem rev26_s0_lr_mem rev26_s0_ul_mem rev26_s0_ur_mem p
    (hp _ rev26_plane55_mem) (hp _ rev26_plane9_mem) hx0 hx1
def rev26_s1_ll : FractionPoint := ⟨31384269691121147,58446316538000000,2593363605042740122157,10195083225306030000000⟩
theorem rev26_s1_ll_mem : rev26_s1_ll.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane55 rev26_vertex2 rev26_vertex3 rev26_s1_ll
    rev26_vertex2_mem rev26_vertex3_mem (by decide)
def rev26_s1_lr : FractionPoint := ⟨8758696339928223,15819173098000000,734259282275019253961,2759417459349630000000⟩
theorem rev26_s1_lr_mem : rev26_s1_lr.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane55 rev26_vertex2 rev26_vertex3 rev26_s1_lr
    rev26_vertex2_mem rev26_vertex3_mem (by decide)
def rev26_s1_ul : FractionPoint := ⟨31384269691121147,58446316538000000,16245980828382513,58446316538000000⟩
theorem rev26_s1_ul_mem : rev26_s1_ul.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane10 rev26_vertex1 rev26_vertex0 rev26_s1_ul
    rev26_vertex1_mem rev26_vertex0_mem (by decide)
def rev26_s1_ur : FractionPoint := ⟨8758696339928223,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev26_s1_ur_mem : rev26_s1_ur.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane10 rev26_vertex1 rev26_vertex0 rev26_s1_ur
    rev26_vertex1_mem rev26_vertex0_mem (by decide)
theorem rev26_slab1 (p : Point) (hp : p∈IntegerCarrier rev26_planes)
    (hx0 : rev26_s1_ll.real.1≤p.1) (hx1 : p.1≤rev26_s1_lr.real.1) :
    p∈rationalHull (fractionRow26.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev26_plane55 rev26_plane10 rev26_s1_ll rev26_s1_lr rev26_s1_ul rev26_s1_ur
    (by decide) rev26_s1_ll_mem rev26_s1_lr_mem rev26_s1_ul_mem rev26_s1_ur_mem p
    (hp _ rev26_plane55_mem) (hp _ rev26_plane10_mem) hx0 hx1
def rev26_s2_ll : FractionPoint := ⟨8758696339928223,15819173098000000,734259282275019253961,2759417459349630000000⟩
theorem rev26_s2_ll_mem : rev26_s2_ll.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane55 rev26_vertex2 rev26_vertex3 rev26_s2_ll
    rev26_vertex2_mem rev26_vertex3_mem (by decide)
def rev26_s2_lr : FractionPoint := ⟨4061837715759,7332499000000,29287950748577,109987485000000⟩
theorem rev26_s2_lr_mem : rev26_s2_lr.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane55 rev26_vertex2 rev26_vertex3 rev26_s2_lr
    rev26_vertex2_mem rev26_vertex3_mem (by decide)
def rev26_s2_ul : FractionPoint := ⟨8758696339928223,15819173098000000,4395604732592341,15819173098000000⟩
theorem rev26_s2_ul_mem : rev26_s2_ul.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane54 rev26_vertex0 rev26_vertex3 rev26_s2_ul
    rev26_vertex0_mem rev26_vertex3_mem (by decide)
def rev26_s2_ur : FractionPoint := ⟨4061837715759,7332499000000,29287950748577,109987485000000⟩
theorem rev26_s2_ur_mem : rev26_s2_ur.real ∈ rationalHull (fractionRow26.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow26 rev26_plane54 rev26_vertex0 rev26_vertex3 rev26_s2_ur
    rev26_vertex0_mem rev26_vertex3_mem (by decide)
theorem rev26_slab2 (p : Point) (hp : p∈IntegerCarrier rev26_planes)
    (hx0 : rev26_s2_ll.real.1≤p.1) (hx1 : p.1≤rev26_s2_lr.real.1) :
    p∈rationalHull (fractionRow26.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev26_plane55 rev26_plane54 rev26_s2_ll rev26_s2_lr rev26_s2_ul rev26_s2_ur
    (by decide) rev26_s2_ll_mem rev26_s2_lr_mem rev26_s2_ul_mem rev26_s2_ur_mem p
    (hp _ rev26_plane55_mem) (hp _ rev26_plane54_mem) hx0 hx1
theorem rev26_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev26_planes) : rev26_s0_ll.real.1≤p.1 := by
  have hc := rev26_plane9.combine_sound rev26_plane55 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev26_plane9_mem) (hp _ rev26_plane55_mem)
  exact (rev26_plane9.combine rev26_plane55 2093220000000 1393416000000).xBoundCheck_sound rev26_s0_ll.nx rev26_s0_ll.dx true (by decide) p hc
theorem rev26_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev26_planes) : p.1≤rev26_s2_lr.real.1 := by
  have hc := rev26_plane54.combine_sound rev26_plane55 2093220000000 51300000000 (by decide) (by decide) p
    (hp _ rev26_plane54_mem) (hp _ rev26_plane55_mem)
  exact (rev26_plane54.combine rev26_plane55 2093220000000 51300000000).xBoundCheck_sound rev26_s2_lr.nx rev26_s2_lr.dx false (by decide) p hc
theorem rev26_hull (p : Point) (hp : p∈IntegerCarrier rev26_planes) :
    p∈rationalHull (fractionRow26.map FractionPoint.rational) := by
  have hxlo := rev26_bound0_lo p hp
  have hxhi := rev26_bound0_hi p hp
  by_cases h0 : p.1≤rev26_s0_lr.real.1
  · exact rev26_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev26_s1_lr.real.1
  · exact rev26_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev26_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull26 (p : Point)
    (hp : ∀ g, ClosedCell ((![2,5,6,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow26 := by
  rw [← fractionRow26_correct]
  exact rev26_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull26
