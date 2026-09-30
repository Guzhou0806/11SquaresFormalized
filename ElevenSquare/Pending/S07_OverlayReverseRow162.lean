import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks20
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev162_planes : List IntegerPlane := integerOverlayPlanes ![10,13,9,6]
def rev162_plane33 : IntegerPlane := ⟨13084000000,(-2218132000000),(-1594545024972)⟩
theorem rev162_plane33_mem : rev162_plane33 ∈ rev162_planes := by decide
def rev162_plane34 : IntegerPlane := ⟨(-2099728000000),(-1393416000000),(-2133599860516)⟩
theorem rev162_plane34_mem : rev162_plane34 ∈ rev162_planes := by decide
def rev162_plane74 : IntegerPlane := ⟨2168356000000,(-51300000000),1163521164456⟩
theorem rev162_plane74_mem : rev162_plane74 ∈ rev162_planes := by decide
def rev162_plane75 : IntegerPlane := ⟨1468788000000,2093220000000,2349463273104⟩
theorem rev162_plane75_mem : rev162_plane75 ∈ rev162_planes := by decide
def rev162_vertex0 : FractionPoint := fractionRow162[0]!
theorem rev162_vertex0_mem : rev162_vertex0∈fractionRow162 := by decide
def rev162_vertex1 : FractionPoint := fractionRow162[1]!
theorem rev162_vertex1_mem : rev162_vertex1∈fractionRow162 := by decide
def rev162_vertex2 : FractionPoint := fractionRow162[2]!
theorem rev162_vertex2_mem : rev162_vertex2∈fractionRow162 := by decide
def rev162_vertex3 : FractionPoint := fractionRow162[3]!
theorem rev162_vertex3_mem : rev162_vertex3∈fractionRow162 := by decide
def rev162_s0_ll : FractionPoint := ⟨8279959610234849,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev162_s0_ll_mem : rev162_s0_ll.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane34 rev162_vertex0 rev162_vertex1 rev162_s0_ll
    rev162_vertex0_mem rev162_vertex1_mem (by decide)
def rev162_s0_lr : FractionPoint := ⟨31384269691121147,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev162_s0_lr_mem : rev162_s0_lr.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane34 rev162_vertex0 rev162_vertex1 rev162_s0_lr
    rev162_vertex0_mem rev162_vertex1_mem (by decide)
def rev162_s0_ul : FractionPoint := ⟨8279959610234849,16309444058000000,37488082241261273,48928332174000000⟩
theorem rev162_s0_ul_mem : rev162_s0_ul.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane75 rev162_vertex0 rev162_vertex3 rev162_s0_ul
    rev162_vertex0_mem rev162_vertex3_mem (by decide)
def rev162_s0_ur : FractionPoint := ⟨31384269691121147,58446316538000000,7601719620263289877843,10195083225306030000000⟩
theorem rev162_s0_ur_mem : rev162_s0_ur.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane75 rev162_vertex0 rev162_vertex3 rev162_s0_ur
    rev162_vertex0_mem rev162_vertex3_mem (by decide)
theorem rev162_slab0 (p : Point) (hp : p∈IntegerCarrier rev162_planes)
    (hx0 : rev162_s0_ll.real.1≤p.1) (hx1 : p.1≤rev162_s0_lr.real.1) :
    p∈rationalHull (fractionRow162.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev162_plane34 rev162_plane75 rev162_s0_ll rev162_s0_lr rev162_s0_ul rev162_s0_ur
    (by decide) rev162_s0_ll_mem rev162_s0_lr_mem rev162_s0_ul_mem rev162_s0_ur_mem p
    (hp _ rev162_plane34_mem) (hp _ rev162_plane75_mem) hx0 hx1
def rev162_s1_ll : FractionPoint := ⟨31384269691121147,58446316538000000,42200335709617487,58446316538000000⟩
theorem rev162_s1_ll_mem : rev162_s1_ll.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane33 rev162_vertex1 rev162_vertex2 rev162_s1_ll
    rev162_vertex1_mem rev162_vertex2_mem (by decide)
def rev162_s1_lr : FractionPoint := ⟨8758696339928223,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev162_s1_lr_mem : rev162_s1_lr.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane33 rev162_vertex1 rev162_vertex2 rev162_s1_lr
    rev162_vertex1_mem rev162_vertex2_mem (by decide)
def rev162_s1_ul : FractionPoint := ⟨31384269691121147,58446316538000000,7601719620263289877843,10195083225306030000000⟩
theorem rev162_s1_ul_mem : rev162_s1_ul.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane75 rev162_vertex0 rev162_vertex3 rev162_s1_ul
    rev162_vertex0_mem rev162_vertex3_mem (by decide)
def rev162_s1_ur : FractionPoint := ⟨8758696339928223,15819173098000000,2025158177074610746039,2759417459349630000000⟩
theorem rev162_s1_ur_mem : rev162_s1_ur.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane75 rev162_vertex0 rev162_vertex3 rev162_s1_ur
    rev162_vertex0_mem rev162_vertex3_mem (by decide)
theorem rev162_slab1 (p : Point) (hp : p∈IntegerCarrier rev162_planes)
    (hx0 : rev162_s1_ll.real.1≤p.1) (hx1 : p.1≤rev162_s1_lr.real.1) :
    p∈rationalHull (fractionRow162.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev162_plane33 rev162_plane75 rev162_s1_ll rev162_s1_lr rev162_s1_ul rev162_s1_ur
    (by decide) rev162_s1_ll_mem rev162_s1_lr_mem rev162_s1_ul_mem rev162_s1_ur_mem p
    (hp _ rev162_plane33_mem) (hp _ rev162_plane75_mem) hx0 hx1
def rev162_s2_ll : FractionPoint := ⟨8758696339928223,15819173098000000,11423568365407659,15819173098000000⟩
theorem rev162_s2_ll_mem : rev162_s2_ll.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane74 rev162_vertex2 rev162_vertex3 rev162_s2_ll
    rev162_vertex2_mem rev162_vertex3_mem (by decide)
def rev162_s2_lr : FractionPoint := ⟨4061837715759,7332499000000,80699534251423,109987485000000⟩
theorem rev162_s2_lr_mem : rev162_s2_lr.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane74 rev162_vertex2 rev162_vertex3 rev162_s2_lr
    rev162_vertex2_mem rev162_vertex3_mem (by decide)
def rev162_s2_ul : FractionPoint := ⟨8758696339928223,15819173098000000,2025158177074610746039,2759417459349630000000⟩
theorem rev162_s2_ul_mem : rev162_s2_ul.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane75 rev162_vertex0 rev162_vertex3 rev162_s2_ul
    rev162_vertex0_mem rev162_vertex3_mem (by decide)
def rev162_s2_ur : FractionPoint := ⟨4061837715759,7332499000000,80699534251423,109987485000000⟩
theorem rev162_s2_ur_mem : rev162_s2_ur.real ∈ rationalHull (fractionRow162.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow162 rev162_plane75 rev162_vertex0 rev162_vertex3 rev162_s2_ur
    rev162_vertex0_mem rev162_vertex3_mem (by decide)
theorem rev162_slab2 (p : Point) (hp : p∈IntegerCarrier rev162_planes)
    (hx0 : rev162_s2_ll.real.1≤p.1) (hx1 : p.1≤rev162_s2_lr.real.1) :
    p∈rationalHull (fractionRow162.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev162_plane74 rev162_plane75 rev162_s2_ll rev162_s2_lr rev162_s2_ul rev162_s2_ur
    (by decide) rev162_s2_ll_mem rev162_s2_lr_mem rev162_s2_ul_mem rev162_s2_ur_mem p
    (hp _ rev162_plane74_mem) (hp _ rev162_plane75_mem) hx0 hx1
theorem rev162_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev162_planes) : rev162_s0_ll.real.1≤p.1 := by
  have hc := rev162_plane34.combine_sound rev162_plane75 2093220000000 1393416000000 (by decide) (by decide) p
    (hp _ rev162_plane34_mem) (hp _ rev162_plane75_mem)
  exact (rev162_plane34.combine rev162_plane75 2093220000000 1393416000000).xBoundCheck_sound rev162_s0_ll.nx rev162_s0_ll.dx true (by decide) p hc
theorem rev162_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev162_planes) : p.1≤rev162_s2_lr.real.1 := by
  have hc := rev162_plane74.combine_sound rev162_plane75 2093220000000 51300000000 (by decide) (by decide) p
    (hp _ rev162_plane74_mem) (hp _ rev162_plane75_mem)
  exact (rev162_plane74.combine rev162_plane75 2093220000000 51300000000).xBoundCheck_sound rev162_s2_lr.nx rev162_s2_lr.dx false (by decide) p hc
theorem rev162_hull (p : Point) (hp : p∈IntegerCarrier rev162_planes) :
    p∈rationalHull (fractionRow162.map FractionPoint.rational) := by
  have hxlo := rev162_bound0_lo p hp
  have hxhi := rev162_bound0_hi p hp
  by_cases h0 : p.1≤rev162_s0_lr.real.1
  · exact rev162_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev162_s1_lr.real.1
  · exact rev162_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev162_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull162 (p : Point)
    (hp : ∀ g, ClosedCell ((![10,13,9,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow162 := by
  rw [← fractionRow162_correct]
  exact rev162_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull162
