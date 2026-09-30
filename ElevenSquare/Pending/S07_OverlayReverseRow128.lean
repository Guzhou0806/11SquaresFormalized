import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks16
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev128_planes : List IntegerPlane := integerOverlayPlanes ![9,6,5,2]
def rev128_plane34 : IntegerPlane := ⟨51300000000,2168356000000,1214821164456⟩
theorem rev128_plane34_mem : rev128_plane34 ∈ rev128_planes := by decide
def rev128_plane35 : IntegerPlane := ⟨(-2093220000000),1468788000000,256243273104⟩
theorem rev128_plane35_mem : rev128_plane35 ∈ rev128_planes := by decide
def rev128_plane69 : IntegerPlane := ⟨1393416000000,(-2099728000000),(-740183860516)⟩
theorem rev128_plane69_mem : rev128_plane69 ∈ rev128_planes := by decide
def rev128_plane70 : IntegerPlane := ⟨2218132000000,13084000000,623586975028⟩
theorem rev128_plane70_mem : rev128_plane70 ∈ rev128_planes := by decide
def rev128_vertex0 : FractionPoint := fractionRow128[0]!
theorem rev128_vertex0_mem : rev128_vertex0∈fractionRow128 := by decide
def rev128_vertex1 : FractionPoint := fractionRow128[1]!
theorem rev128_vertex1_mem : rev128_vertex1∈fractionRow128 := by decide
def rev128_vertex2 : FractionPoint := fractionRow128[2]!
theorem rev128_vertex2_mem : rev128_vertex2∈fractionRow128 := by decide
def rev128_vertex3 : FractionPoint := fractionRow128[3]!
theorem rev128_vertex3_mem : rev128_vertex3∈fractionRow128 := by decide
def rev128_s0_ll : FractionPoint := ⟨11440249932738727,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev128_s0_ll_mem : rev128_s0_ll.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane69 rev128_vertex2 rev128_vertex3 rev128_s0_ll
    rev128_vertex2_mem rev128_vertex3_mem (by decide)
def rev128_s0_lr : FractionPoint := ⟨29287950748577,109987485000000,10185105036335400941,19245316825340000000⟩
theorem rev128_s0_lr_mem : rev128_s0_lr.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane69 rev128_vertex2 rev128_vertex3 rev128_s0_lr
    rev128_vertex2_mem rev128_vertex3_mem (by decide)
def rev128_s0_ul : FractionPoint := ⟨11440249932738727,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev128_s0_ul_mem : rev128_s0_ul.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane35 rev128_vertex2 rev128_vertex1 rev128_s0_ul
    rev128_vertex2_mem rev128_vertex1_mem (by decide)
def rev128_s0_ur : FractionPoint := ⟨29287950748577,109987485000000,4061837715759,7332499000000⟩
theorem rev128_s0_ur_mem : rev128_s0_ur.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane35 rev128_vertex2 rev128_vertex1 rev128_s0_ur
    rev128_vertex2_mem rev128_vertex1_mem (by decide)
theorem rev128_slab0 (p : Point) (hp : p∈IntegerCarrier rev128_planes)
    (hx0 : rev128_s0_ll.real.1≤p.1) (hx1 : p.1≤rev128_s0_lr.real.1) :
    p∈rationalHull (fractionRow128.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev128_plane69 rev128_plane35 rev128_s0_ll rev128_s0_lr rev128_s0_ul rev128_s0_ur
    (by decide) rev128_s0_ll_mem rev128_s0_lr_mem rev128_s0_ul_mem rev128_s0_ur_mem p
    (hp _ rev128_plane69_mem) (hp _ rev128_plane35_mem) hx0 hx1
def rev128_s1_ll : FractionPoint := ⟨29287950748577,109987485000000,10185105036335400941,19245316825340000000⟩
theorem rev128_s1_ll_mem : rev128_s1_ll.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane69 rev128_vertex2 rev128_vertex3 rev128_s1_ll
    rev128_vertex2_mem rev128_vertex3_mem (by decide)
def rev128_s1_lr : FractionPoint := ⟨4395604732592341,15819173098000000,1114625161119898814089,2075997543169834000000⟩
theorem rev128_s1_lr_mem : rev128_s1_lr.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane69 rev128_vertex2 rev128_vertex3 rev128_s1_lr
    rev128_vertex2_mem rev128_vertex3_mem (by decide)
def rev128_s1_ul : FractionPoint := ⟨29287950748577,109987485000000,4061837715759,7332499000000⟩
theorem rev128_s1_ul_mem : rev128_s1_ul.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane34 rev128_vertex1 rev128_vertex0 rev128_s1_ul
    rev128_vertex1_mem rev128_vertex0_mem (by decide)
def rev128_s1_ur : FractionPoint := ⟨4395604732592341,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev128_s1_ur_mem : rev128_s1_ur.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane34 rev128_vertex1 rev128_vertex0 rev128_s1_ur
    rev128_vertex1_mem rev128_vertex0_mem (by decide)
theorem rev128_slab1 (p : Point) (hp : p∈IntegerCarrier rev128_planes)
    (hx0 : rev128_s1_ll.real.1≤p.1) (hx1 : p.1≤rev128_s1_lr.real.1) :
    p∈rationalHull (fractionRow128.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev128_plane69 rev128_plane34 rev128_s1_ll rev128_s1_lr rev128_s1_ul rev128_s1_ur
    (by decide) rev128_s1_ll_mem rev128_s1_lr_mem rev128_s1_ul_mem rev128_s1_ur_mem p
    (hp _ rev128_plane69_mem) (hp _ rev128_plane34_mem) hx0 hx1
def rev128_s2_ll : FractionPoint := ⟨4395604732592341,15819173098000000,1114625161119898814089,2075997543169834000000⟩
theorem rev128_s2_ll_mem : rev128_s2_ll.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane69 rev128_vertex2 rev128_vertex3 rev128_s2_ll
    rev128_vertex2_mem rev128_vertex3_mem (by decide)
def rev128_s2_lr : FractionPoint := ⟨16245980828382513,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev128_s2_lr_mem : rev128_s2_lr.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane69 rev128_vertex2 rev128_vertex3 rev128_s2_lr
    rev128_vertex2_mem rev128_vertex3_mem (by decide)
def rev128_s2_ul : FractionPoint := ⟨4395604732592341,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev128_s2_ul_mem : rev128_s2_ul.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane70 rev128_vertex0 rev128_vertex3 rev128_s2_ul
    rev128_vertex0_mem rev128_vertex3_mem (by decide)
def rev128_s2_ur : FractionPoint := ⟨16245980828382513,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev128_s2_ur_mem : rev128_s2_ur.real ∈ rationalHull (fractionRow128.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow128 rev128_plane70 rev128_vertex0 rev128_vertex3 rev128_s2_ur
    rev128_vertex0_mem rev128_vertex3_mem (by decide)
theorem rev128_slab2 (p : Point) (hp : p∈IntegerCarrier rev128_planes)
    (hx0 : rev128_s2_ll.real.1≤p.1) (hx1 : p.1≤rev128_s2_lr.real.1) :
    p∈rationalHull (fractionRow128.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev128_plane69 rev128_plane70 rev128_s2_ll rev128_s2_lr rev128_s2_ul rev128_s2_ur
    (by decide) rev128_s2_ll_mem rev128_s2_lr_mem rev128_s2_ul_mem rev128_s2_ur_mem p
    (hp _ rev128_plane69_mem) (hp _ rev128_plane70_mem) hx0 hx1
theorem rev128_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev128_planes) : rev128_s0_ll.real.1≤p.1 := by
  have hc := rev128_plane35.combine_sound rev128_plane69 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev128_plane35_mem) (hp _ rev128_plane69_mem)
  exact (rev128_plane35.combine rev128_plane69 2099728000000 1468788000000).xBoundCheck_sound rev128_s0_ll.nx rev128_s0_ll.dx true (by decide) p hc
theorem rev128_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev128_planes) : p.1≤rev128_s2_lr.real.1 := by
  have hc := rev128_plane69.combine_sound rev128_plane70 13084000000 2099728000000 (by decide) (by decide) p
    (hp _ rev128_plane69_mem) (hp _ rev128_plane70_mem)
  exact (rev128_plane69.combine rev128_plane70 13084000000 2099728000000).xBoundCheck_sound rev128_s2_lr.nx rev128_s2_lr.dx false (by decide) p hc
theorem rev128_hull (p : Point) (hp : p∈IntegerCarrier rev128_planes) :
    p∈rationalHull (fractionRow128.map FractionPoint.rational) := by
  have hxlo := rev128_bound0_lo p hp
  have hxhi := rev128_bound0_hi p hp
  by_cases h0 : p.1≤rev128_s0_lr.real.1
  · exact rev128_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev128_s1_lr.real.1
  · exact rev128_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev128_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull128 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,6,5,2] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow128 := by
  rw [← fractionRow128_correct]
  exact rev128_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull128
