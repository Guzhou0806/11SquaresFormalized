import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks11
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev91_planes : List IntegerPlane := integerOverlayPlanes ![6,9,10,13]
def rev91_plane28 : IntegerPlane := ⟨2093220000000,(-1468788000000),880675273104⟩
theorem rev91_plane28_mem : rev91_plane28 ∈ rev91_planes := by decide
def rev91_plane29 : IntegerPlane := ⟨(-51300000000),(-2168356000000),(-1004834835544)⟩
theorem rev91_plane29_mem : rev91_plane29 ∈ rev91_planes := by decide
def rev91_plane73 : IntegerPlane := ⟨(-2218132000000),(-13084000000),(-1607629024972)⟩
theorem rev91_plane73_mem : rev91_plane73 ∈ rev91_planes := by decide
def rev91_plane74 : IntegerPlane := ⟨(-1393416000000),2099728000000,(-33871860516)⟩
theorem rev91_plane74_mem : rev91_plane74 ∈ rev91_planes := by decide
def rev91_vertex0 : FractionPoint := fractionRow91[0]!
theorem rev91_vertex0_mem : rev91_vertex0∈fractionRow91 := by decide
def rev91_vertex1 : FractionPoint := fractionRow91[1]!
theorem rev91_vertex1_mem : rev91_vertex1∈fractionRow91 := by decide
def rev91_vertex2 : FractionPoint := fractionRow91[2]!
theorem rev91_vertex2_mem : rev91_vertex2∈fractionRow91 := by decide
def rev91_vertex3 : FractionPoint := fractionRow91[3]!
theorem rev91_vertex3_mem : rev91_vertex3∈fractionRow91 := by decide
def rev91_s0_ll : FractionPoint := ⟨42200335709617487,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev91_s0_ll_mem : rev91_s0_ll.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane73 rev91_vertex3 rev91_vertex0 rev91_s0_ll
    rev91_vertex3_mem rev91_vertex0_mem (by decide)
def rev91_s0_lr : FractionPoint := ⟨11423568365407659,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev91_s0_lr_mem : rev91_s0_lr.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane73 rev91_vertex3 rev91_vertex0 rev91_s0_lr
    rev91_vertex3_mem rev91_vertex0_mem (by decide)
def rev91_s0_ul : FractionPoint := ⟨42200335709617487,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev91_s0_ul_mem : rev91_s0_ul.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane74 rev91_vertex3 rev91_vertex2 rev91_s0_ul
    rev91_vertex3_mem rev91_vertex2_mem (by decide)
def rev91_s0_ur : FractionPoint := ⟨11423568365407659,15819173098000000,961372382049935185911,2075997543169834000000⟩
theorem rev91_s0_ur_mem : rev91_s0_ur.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane74 rev91_vertex3 rev91_vertex2 rev91_s0_ur
    rev91_vertex3_mem rev91_vertex2_mem (by decide)
theorem rev91_slab0 (p : Point) (hp : p∈IntegerCarrier rev91_planes)
    (hx0 : rev91_s0_ll.real.1≤p.1) (hx1 : p.1≤rev91_s0_lr.real.1) :
    p∈rationalHull (fractionRow91.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev91_plane73 rev91_plane74 rev91_s0_ll rev91_s0_lr rev91_s0_ul rev91_s0_ur
    (by decide) rev91_s0_ll_mem rev91_s0_lr_mem rev91_s0_ul_mem rev91_s0_ur_mem p
    (hp _ rev91_plane73_mem) (hp _ rev91_plane74_mem) hx0 hx1
def rev91_s1_ll : FractionPoint := ⟨11423568365407659,15819173098000000,7060476758071777,15819173098000000⟩
theorem rev91_s1_ll_mem : rev91_s1_ll.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane29 rev91_vertex0 rev91_vertex1 rev91_s1_ll
    rev91_vertex0_mem rev91_vertex1_mem (by decide)
def rev91_s1_lr : FractionPoint := ⟨80699534251423,109987485000000,3270661284241,7332499000000⟩
theorem rev91_s1_lr_mem : rev91_s1_lr.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane29 rev91_vertex0 rev91_vertex1 rev91_s1_lr
    rev91_vertex0_mem rev91_vertex1_mem (by decide)
def rev91_s1_ul : FractionPoint := ⟨11423568365407659,15819173098000000,961372382049935185911,2075997543169834000000⟩
theorem rev91_s1_ul_mem : rev91_s1_ul.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane74 rev91_vertex3 rev91_vertex2 rev91_s1_ul
    rev91_vertex3_mem rev91_vertex2_mem (by decide)
def rev91_s1_ur : FractionPoint := ⟨80699534251423,109987485000000,9060211789004599059,19245316825340000000⟩
theorem rev91_s1_ur_mem : rev91_s1_ur.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane74 rev91_vertex3 rev91_vertex2 rev91_s1_ur
    rev91_vertex3_mem rev91_vertex2_mem (by decide)
theorem rev91_slab1 (p : Point) (hp : p∈IntegerCarrier rev91_planes)
    (hx0 : rev91_s1_ll.real.1≤p.1) (hx1 : p.1≤rev91_s1_lr.real.1) :
    p∈rationalHull (fractionRow91.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev91_plane29 rev91_plane74 rev91_s1_ll rev91_s1_lr rev91_s1_ul rev91_s1_ur
    (by decide) rev91_s1_ll_mem rev91_s1_lr_mem rev91_s1_ul_mem rev91_s1_ur_mem p
    (hp _ rev91_plane29_mem) (hp _ rev91_plane74_mem) hx0 hx1
def rev91_s2_ll : FractionPoint := ⟨80699534251423,109987485000000,3270661284241,7332499000000⟩
theorem rev91_s2_ll_mem : rev91_s2_ll.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane28 rev91_vertex1 rev91_vertex2 rev91_s2_ll
    rev91_vertex1_mem rev91_vertex2_mem (by decide)
def rev91_s2_lr : FractionPoint := ⟨37488082241261273,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev91_s2_lr_mem : rev91_s2_lr.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane28 rev91_vertex1 rev91_vertex2 rev91_s2_lr
    rev91_vertex1_mem rev91_vertex2_mem (by decide)
def rev91_s2_ul : FractionPoint := ⟨80699534251423,109987485000000,9060211789004599059,19245316825340000000⟩
theorem rev91_s2_ul_mem : rev91_s2_ul.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane74 rev91_vertex3 rev91_vertex2 rev91_s2_ul
    rev91_vertex3_mem rev91_vertex2_mem (by decide)
def rev91_s2_ur : FractionPoint := ⟨37488082241261273,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev91_s2_ur_mem : rev91_s2_ur.real ∈ rationalHull (fractionRow91.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow91 rev91_plane74 rev91_vertex3 rev91_vertex2 rev91_s2_ur
    rev91_vertex3_mem rev91_vertex2_mem (by decide)
theorem rev91_slab2 (p : Point) (hp : p∈IntegerCarrier rev91_planes)
    (hx0 : rev91_s2_ll.real.1≤p.1) (hx1 : p.1≤rev91_s2_lr.real.1) :
    p∈rationalHull (fractionRow91.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev91_plane28 rev91_plane74 rev91_s2_ll rev91_s2_lr rev91_s2_ul rev91_s2_ur
    (by decide) rev91_s2_ll_mem rev91_s2_lr_mem rev91_s2_ul_mem rev91_s2_ur_mem p
    (hp _ rev91_plane28_mem) (hp _ rev91_plane74_mem) hx0 hx1
theorem rev91_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev91_planes) : rev91_s0_ll.real.1≤p.1 := by
  have hc := rev91_plane73.combine_sound rev91_plane74 2099728000000 13084000000 (by decide) (by decide) p
    (hp _ rev91_plane73_mem) (hp _ rev91_plane74_mem)
  exact (rev91_plane73.combine rev91_plane74 2099728000000 13084000000).xBoundCheck_sound rev91_s0_ll.nx rev91_s0_ll.dx true (by decide) p hc
theorem rev91_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev91_planes) : p.1≤rev91_s2_lr.real.1 := by
  have hc := rev91_plane28.combine_sound rev91_plane74 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev91_plane28_mem) (hp _ rev91_plane74_mem)
  exact (rev91_plane28.combine rev91_plane74 2099728000000 1468788000000).xBoundCheck_sound rev91_s2_lr.nx rev91_s2_lr.dx false (by decide) p hc
theorem rev91_hull (p : Point) (hp : p∈IntegerCarrier rev91_planes) :
    p∈rationalHull (fractionRow91.map FractionPoint.rational) := by
  have hxlo := rev91_bound0_lo p hp
  have hxhi := rev91_bound0_hi p hp
  by_cases h0 : p.1≤rev91_s0_lr.real.1
  · exact rev91_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev91_s1_lr.real.1
  · exact rev91_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev91_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull91 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,9,10,13] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow91 := by
  rw [← fractionRow91_correct]
  exact rev91_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull91
