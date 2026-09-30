import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks15
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev127_planes : List IntegerPlane := integerOverlayPlanes ![9,6,2,5]
def rev127_plane8 : IntegerPlane := ⟨(-2093220000000),(-1468788000000),(-1212544726896)⟩
theorem rev127_plane8_mem : rev127_plane8 ∈ rev127_planes := by decide
def rev127_plane9 : IntegerPlane := ⟨51300000000,(-2168356000000),(-953534835544)⟩
theorem rev127_plane9_mem : rev127_plane9 ∈ rev127_planes := by decide
def rev127_plane49 : IntegerPlane := ⟨1393416000000,2099728000000,1359544139484⟩
theorem rev127_plane49_mem : rev127_plane49 ∈ rev127_planes := by decide
def rev127_plane50 : IntegerPlane := ⟨2218132000000,(-13084000000),610502975028⟩
theorem rev127_plane50_mem : rev127_plane50 ∈ rev127_planes := by decide
def rev127_vertex0 : FractionPoint := fractionRow127[0]!
theorem rev127_vertex0_mem : rev127_vertex0∈fractionRow127 := by decide
def rev127_vertex1 : FractionPoint := fractionRow127[1]!
theorem rev127_vertex1_mem : rev127_vertex1∈fractionRow127 := by decide
def rev127_vertex2 : FractionPoint := fractionRow127[2]!
theorem rev127_vertex2_mem : rev127_vertex2∈fractionRow127 := by decide
def rev127_vertex3 : FractionPoint := fractionRow127[3]!
theorem rev127_vertex3_mem : rev127_vertex3∈fractionRow127 := by decide
def rev127_s0_ll : FractionPoint := ⟨11440249932738727,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev127_s0_ll_mem : rev127_s0_ll.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane8 rev127_vertex0 rev127_vertex1 rev127_s0_ll
    rev127_vertex0_mem rev127_vertex1_mem (by decide)
def rev127_s0_lr : FractionPoint := ⟨29287950748577,109987485000000,3270661284241,7332499000000⟩
theorem rev127_s0_lr_mem : rev127_s0_lr.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane8 rev127_vertex0 rev127_vertex1 rev127_s0_lr
    rev127_vertex0_mem rev127_vertex1_mem (by decide)
def rev127_s0_ul : FractionPoint := ⟨11440249932738727,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev127_s0_ul_mem : rev127_s0_ul.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane49 rev127_vertex0 rev127_vertex3 rev127_s0_ul
    rev127_vertex0_mem rev127_vertex3_mem (by decide)
def rev127_s0_ur : FractionPoint := ⟨29287950748577,109987485000000,9060211789004599059,19245316825340000000⟩
theorem rev127_s0_ur_mem : rev127_s0_ur.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane49 rev127_vertex0 rev127_vertex3 rev127_s0_ur
    rev127_vertex0_mem rev127_vertex3_mem (by decide)
theorem rev127_slab0 (p : Point) (hp : p∈IntegerCarrier rev127_planes)
    (hx0 : rev127_s0_ll.real.1≤p.1) (hx1 : p.1≤rev127_s0_lr.real.1) :
    p∈rationalHull (fractionRow127.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev127_plane8 rev127_plane49 rev127_s0_ll rev127_s0_lr rev127_s0_ul rev127_s0_ur
    (by decide) rev127_s0_ll_mem rev127_s0_lr_mem rev127_s0_ul_mem rev127_s0_ur_mem p
    (hp _ rev127_plane8_mem) (hp _ rev127_plane49_mem) hx0 hx1
def rev127_s1_ll : FractionPoint := ⟨29287950748577,109987485000000,3270661284241,7332499000000⟩
theorem rev127_s1_ll_mem : rev127_s1_ll.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane9 rev127_vertex1 rev127_vertex2 rev127_s1_ll
    rev127_vertex1_mem rev127_vertex2_mem (by decide)
def rev127_s1_lr : FractionPoint := ⟨4395604732592341,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev127_s1_lr_mem : rev127_s1_lr.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane9 rev127_vertex1 rev127_vertex2 rev127_s1_lr
    rev127_vertex1_mem rev127_vertex2_mem (by decide)
def rev127_s1_ul : FractionPoint := ⟨29287950748577,109987485000000,9060211789004599059,19245316825340000000⟩
theorem rev127_s1_ul_mem : rev127_s1_ul.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane49 rev127_vertex0 rev127_vertex3 rev127_s1_ul
    rev127_vertex0_mem rev127_vertex3_mem (by decide)
def rev127_s1_ur : FractionPoint := ⟨4395604732592341,15819173098000000,961372382049935185911,2075997543169834000000⟩
theorem rev127_s1_ur_mem : rev127_s1_ur.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane49 rev127_vertex0 rev127_vertex3 rev127_s1_ur
    rev127_vertex0_mem rev127_vertex3_mem (by decide)
theorem rev127_slab1 (p : Point) (hp : p∈IntegerCarrier rev127_planes)
    (hx0 : rev127_s1_ll.real.1≤p.1) (hx1 : p.1≤rev127_s1_lr.real.1) :
    p∈rationalHull (fractionRow127.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev127_plane9 rev127_plane49 rev127_s1_ll rev127_s1_lr rev127_s1_ul rev127_s1_ur
    (by decide) rev127_s1_ll_mem rev127_s1_lr_mem rev127_s1_ul_mem rev127_s1_ur_mem p
    (hp _ rev127_plane9_mem) (hp _ rev127_plane49_mem) hx0 hx1
def rev127_s2_ll : FractionPoint := ⟨4395604732592341,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev127_s2_ll_mem : rev127_s2_ll.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane50 rev127_vertex2 rev127_vertex3 rev127_s2_ll
    rev127_vertex2_mem rev127_vertex3_mem (by decide)
def rev127_s2_lr : FractionPoint := ⟨16245980828382513,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev127_s2_lr_mem : rev127_s2_lr.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane50 rev127_vertex2 rev127_vertex3 rev127_s2_lr
    rev127_vertex2_mem rev127_vertex3_mem (by decide)
def rev127_s2_ul : FractionPoint := ⟨4395604732592341,15819173098000000,961372382049935185911,2075997543169834000000⟩
theorem rev127_s2_ul_mem : rev127_s2_ul.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane49 rev127_vertex0 rev127_vertex3 rev127_s2_ul
    rev127_vertex0_mem rev127_vertex3_mem (by decide)
def rev127_s2_ur : FractionPoint := ⟨16245980828382513,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev127_s2_ur_mem : rev127_s2_ur.real ∈ rationalHull (fractionRow127.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow127 rev127_plane49 rev127_vertex0 rev127_vertex3 rev127_s2_ur
    rev127_vertex0_mem rev127_vertex3_mem (by decide)
theorem rev127_slab2 (p : Point) (hp : p∈IntegerCarrier rev127_planes)
    (hx0 : rev127_s2_ll.real.1≤p.1) (hx1 : p.1≤rev127_s2_lr.real.1) :
    p∈rationalHull (fractionRow127.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev127_plane50 rev127_plane49 rev127_s2_ll rev127_s2_lr rev127_s2_ul rev127_s2_ur
    (by decide) rev127_s2_ll_mem rev127_s2_lr_mem rev127_s2_ul_mem rev127_s2_ur_mem p
    (hp _ rev127_plane50_mem) (hp _ rev127_plane49_mem) hx0 hx1
theorem rev127_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev127_planes) : rev127_s0_ll.real.1≤p.1 := by
  have hc := rev127_plane8.combine_sound rev127_plane49 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev127_plane8_mem) (hp _ rev127_plane49_mem)
  exact (rev127_plane8.combine rev127_plane49 2099728000000 1468788000000).xBoundCheck_sound rev127_s0_ll.nx rev127_s0_ll.dx true (by decide) p hc
theorem rev127_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev127_planes) : p.1≤rev127_s2_lr.real.1 := by
  have hc := rev127_plane49.combine_sound rev127_plane50 13084000000 2099728000000 (by decide) (by decide) p
    (hp _ rev127_plane49_mem) (hp _ rev127_plane50_mem)
  exact (rev127_plane49.combine rev127_plane50 13084000000 2099728000000).xBoundCheck_sound rev127_s2_lr.nx rev127_s2_lr.dx false (by decide) p hc
theorem rev127_hull (p : Point) (hp : p∈IntegerCarrier rev127_planes) :
    p∈rationalHull (fractionRow127.map FractionPoint.rational) := by
  have hxlo := rev127_bound0_lo p hp
  have hxhi := rev127_bound0_hi p hp
  by_cases h0 : p.1≤rev127_s0_lr.real.1
  · exact rev127_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev127_s1_lr.real.1
  · exact rev127_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev127_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull127 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,6,2,5] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow127 := by
  rw [← fractionRow127_correct]
  exact rev127_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull127
