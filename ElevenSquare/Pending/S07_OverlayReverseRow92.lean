import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks11
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev92_planes : List IntegerPlane := integerOverlayPlanes ![6,9,13,10]
def rev92_plane14 : IntegerPlane := ⟨(-51300000000),2168356000000,1163521164456⟩
theorem rev92_plane14_mem : rev92_plane14 ∈ rev92_planes := by decide
def rev92_plane15 : IntegerPlane := ⟨2093220000000,1468788000000,2349463273104⟩
theorem rev92_plane15_mem : rev92_plane15 ∈ rev92_planes := by decide
def rev92_plane53 : IntegerPlane := ⟨(-2218132000000),13084000000,(-1594545024972)⟩
theorem rev92_plane53_mem : rev92_plane53 ∈ rev92_planes := by decide
def rev92_plane54 : IntegerPlane := ⟨(-1393416000000),(-2099728000000),(-2133599860516)⟩
theorem rev92_plane54_mem : rev92_plane54 ∈ rev92_planes := by decide
def rev92_vertex0 : FractionPoint := fractionRow92[0]!
theorem rev92_vertex0_mem : rev92_vertex0∈fractionRow92 := by decide
def rev92_vertex1 : FractionPoint := fractionRow92[1]!
theorem rev92_vertex1_mem : rev92_vertex1∈fractionRow92 := by decide
def rev92_vertex2 : FractionPoint := fractionRow92[2]!
theorem rev92_vertex2_mem : rev92_vertex2∈fractionRow92 := by decide
def rev92_vertex3 : FractionPoint := fractionRow92[3]!
theorem rev92_vertex3_mem : rev92_vertex3∈fractionRow92 := by decide
def rev92_s0_ll : FractionPoint := ⟨42200335709617487,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev92_s0_ll_mem : rev92_s0_ll.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane54 rev92_vertex3 rev92_vertex0 rev92_s0_ll
    rev92_vertex3_mem rev92_vertex0_mem (by decide)
def rev92_s0_lr : FractionPoint := ⟨11423568365407659,15819173098000000,1114625161119898814089,2075997543169834000000⟩
theorem rev92_s0_lr_mem : rev92_s0_lr.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane54 rev92_vertex3 rev92_vertex0 rev92_s0_lr
    rev92_vertex3_mem rev92_vertex0_mem (by decide)
def rev92_s0_ul : FractionPoint := ⟨42200335709617487,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev92_s0_ul_mem : rev92_s0_ul.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane53 rev92_vertex3 rev92_vertex2 rev92_s0_ul
    rev92_vertex3_mem rev92_vertex2_mem (by decide)
def rev92_s0_ur : FractionPoint := ⟨11423568365407659,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev92_s0_ur_mem : rev92_s0_ur.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane53 rev92_vertex3 rev92_vertex2 rev92_s0_ur
    rev92_vertex3_mem rev92_vertex2_mem (by decide)
theorem rev92_slab0 (p : Point) (hp : p∈IntegerCarrier rev92_planes)
    (hx0 : rev92_s0_ll.real.1≤p.1) (hx1 : p.1≤rev92_s0_lr.real.1) :
    p∈rationalHull (fractionRow92.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev92_plane54 rev92_plane53 rev92_s0_ll rev92_s0_lr rev92_s0_ul rev92_s0_ur
    (by decide) rev92_s0_ll_mem rev92_s0_lr_mem rev92_s0_ul_mem rev92_s0_ur_mem p
    (hp _ rev92_plane54_mem) (hp _ rev92_plane53_mem) hx0 hx1
def rev92_s1_ll : FractionPoint := ⟨11423568365407659,15819173098000000,1114625161119898814089,2075997543169834000000⟩
theorem rev92_s1_ll_mem : rev92_s1_ll.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane54 rev92_vertex3 rev92_vertex0 rev92_s1_ll
    rev92_vertex3_mem rev92_vertex0_mem (by decide)
def rev92_s1_lr : FractionPoint := ⟨80699534251423,109987485000000,10185105036335400941,19245316825340000000⟩
theorem rev92_s1_lr_mem : rev92_s1_lr.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane54 rev92_vertex3 rev92_vertex0 rev92_s1_lr
    rev92_vertex3_mem rev92_vertex0_mem (by decide)
def rev92_s1_ul : FractionPoint := ⟨11423568365407659,15819173098000000,8758696339928223,15819173098000000⟩
theorem rev92_s1_ul_mem : rev92_s1_ul.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane14 rev92_vertex2 rev92_vertex1 rev92_s1_ul
    rev92_vertex2_mem rev92_vertex1_mem (by decide)
def rev92_s1_ur : FractionPoint := ⟨80699534251423,109987485000000,4061837715759,7332499000000⟩
theorem rev92_s1_ur_mem : rev92_s1_ur.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane14 rev92_vertex2 rev92_vertex1 rev92_s1_ur
    rev92_vertex2_mem rev92_vertex1_mem (by decide)
theorem rev92_slab1 (p : Point) (hp : p∈IntegerCarrier rev92_planes)
    (hx0 : rev92_s1_ll.real.1≤p.1) (hx1 : p.1≤rev92_s1_lr.real.1) :
    p∈rationalHull (fractionRow92.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev92_plane54 rev92_plane14 rev92_s1_ll rev92_s1_lr rev92_s1_ul rev92_s1_ur
    (by decide) rev92_s1_ll_mem rev92_s1_lr_mem rev92_s1_ul_mem rev92_s1_ur_mem p
    (hp _ rev92_plane54_mem) (hp _ rev92_plane14_mem) hx0 hx1
def rev92_s2_ll : FractionPoint := ⟨80699534251423,109987485000000,10185105036335400941,19245316825340000000⟩
theorem rev92_s2_ll_mem : rev92_s2_ll.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane54 rev92_vertex3 rev92_vertex0 rev92_s2_ll
    rev92_vertex3_mem rev92_vertex0_mem (by decide)
def rev92_s2_lr : FractionPoint := ⟨37488082241261273,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev92_s2_lr_mem : rev92_s2_lr.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane54 rev92_vertex3 rev92_vertex0 rev92_s2_lr
    rev92_vertex3_mem rev92_vertex0_mem (by decide)
def rev92_s2_ul : FractionPoint := ⟨80699534251423,109987485000000,4061837715759,7332499000000⟩
theorem rev92_s2_ul_mem : rev92_s2_ul.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane15 rev92_vertex1 rev92_vertex0 rev92_s2_ul
    rev92_vertex1_mem rev92_vertex0_mem (by decide)
def rev92_s2_ur : FractionPoint := ⟨37488082241261273,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev92_s2_ur_mem : rev92_s2_ur.real ∈ rationalHull (fractionRow92.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow92 rev92_plane15 rev92_vertex1 rev92_vertex0 rev92_s2_ur
    rev92_vertex1_mem rev92_vertex0_mem (by decide)
theorem rev92_slab2 (p : Point) (hp : p∈IntegerCarrier rev92_planes)
    (hx0 : rev92_s2_ll.real.1≤p.1) (hx1 : p.1≤rev92_s2_lr.real.1) :
    p∈rationalHull (fractionRow92.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev92_plane54 rev92_plane15 rev92_s2_ll rev92_s2_lr rev92_s2_ul rev92_s2_ur
    (by decide) rev92_s2_ll_mem rev92_s2_lr_mem rev92_s2_ul_mem rev92_s2_ur_mem p
    (hp _ rev92_plane54_mem) (hp _ rev92_plane15_mem) hx0 hx1
theorem rev92_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev92_planes) : rev92_s0_ll.real.1≤p.1 := by
  have hc := rev92_plane53.combine_sound rev92_plane54 2099728000000 13084000000 (by decide) (by decide) p
    (hp _ rev92_plane53_mem) (hp _ rev92_plane54_mem)
  exact (rev92_plane53.combine rev92_plane54 2099728000000 13084000000).xBoundCheck_sound rev92_s0_ll.nx rev92_s0_ll.dx true (by decide) p hc
theorem rev92_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev92_planes) : p.1≤rev92_s2_lr.real.1 := by
  have hc := rev92_plane15.combine_sound rev92_plane54 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev92_plane15_mem) (hp _ rev92_plane54_mem)
  exact (rev92_plane15.combine rev92_plane54 2099728000000 1468788000000).xBoundCheck_sound rev92_s2_lr.nx rev92_s2_lr.dx false (by decide) p hc
theorem rev92_hull (p : Point) (hp : p∈IntegerCarrier rev92_planes) :
    p∈rationalHull (fractionRow92.map FractionPoint.rational) := by
  have hxlo := rev92_bound0_lo p hp
  have hxhi := rev92_bound0_hi p hp
  by_cases h0 : p.1≤rev92_s0_lr.real.1
  · exact rev92_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev92_s1_lr.real.1
  · exact rev92_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev92_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull92 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,9,13,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow92 := by
  rw [← fractionRow92_correct]
  exact rev92_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull92
