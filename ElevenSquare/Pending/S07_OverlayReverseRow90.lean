import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks11
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev90_planes : List IntegerPlane := integerOverlayPlanes ![6,9,10,10]
def rev90_plane15 : IntegerPlane := ⟨2093220000000,1468788000000,2349463273104⟩
theorem rev90_plane15_mem : rev90_plane15 ∈ rev90_planes := by decide
def rev90_plane28 : IntegerPlane := ⟨2093220000000,(-1468788000000),880675273104⟩
theorem rev90_plane28_mem : rev90_plane28 ∈ rev90_planes := by decide
def rev90_plane53 : IntegerPlane := ⟨(-824716000000),2112812000000,539054835544⟩
theorem rev90_plane53_mem : rev90_plane53 ∈ rev90_planes := by decide
def rev90_plane57 : IntegerPlane := ⟨1393416000000,2099728000000,2133599860516⟩
theorem rev90_plane57_mem : rev90_plane57 ∈ rev90_planes := by decide
def rev90_plane73 : IntegerPlane := ⟨(-824716000000),(-2112812000000),(-1573757164456)⟩
theorem rev90_plane73_mem : rev90_plane73 ∈ rev90_planes := by decide
def rev90_plane77 : IntegerPlane := ⟨1393416000000,(-2099728000000),33871860516⟩
theorem rev90_plane77_mem : rev90_plane77 ∈ rev90_planes := by decide
def rev90_vertex0 : FractionPoint := fractionRow90[0]!
theorem rev90_vertex0_mem : rev90_vertex0∈fractionRow90 := by decide
def rev90_vertex1 : FractionPoint := fractionRow90[1]!
theorem rev90_vertex1_mem : rev90_vertex1∈fractionRow90 := by decide
def rev90_vertex2 : FractionPoint := fractionRow90[2]!
theorem rev90_vertex2_mem : rev90_vertex2∈fractionRow90 := by decide
def rev90_vertex3 : FractionPoint := fractionRow90[3]!
theorem rev90_vertex3_mem : rev90_vertex3∈fractionRow90 := by decide
def rev90_vertex4 : FractionPoint := fractionRow90[4]!
theorem rev90_vertex4_mem : rev90_vertex4∈fractionRow90 := by decide
def rev90_vertex5 : FractionPoint := fractionRow90[5]!
theorem rev90_vertex5_mem : rev90_vertex5∈fractionRow90 := by decide
def rev90_s0_ll : FractionPoint := ⟨64668895557,103089500000,1,2⟩
theorem rev90_s0_ll_mem : rev90_s0_ll.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane73 rev90_vertex4 rev90_vertex5 rev90_s0_ll
    rev90_vertex4_mem rev90_vertex5_mem (by decide)
def rev90_s0_lr : FractionPoint := ⟨42200335709617487,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev90_s0_lr_mem : rev90_s0_lr.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane73 rev90_vertex4 rev90_vertex5 rev90_s0_lr
    rev90_vertex4_mem rev90_vertex5_mem (by decide)
def rev90_s0_ul : FractionPoint := ⟨64668895557,103089500000,1,2⟩
theorem rev90_s0_ul_mem : rev90_s0_ul.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane53 rev90_vertex4 rev90_vertex3 rev90_s0_ul
    rev90_vertex4_mem rev90_vertex3_mem (by decide)
def rev90_s0_ur : FractionPoint := ⟨42200335709617487,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev90_s0_ur_mem : rev90_s0_ur.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane53 rev90_vertex4 rev90_vertex3 rev90_s0_ur
    rev90_vertex4_mem rev90_vertex3_mem (by decide)
theorem rev90_slab0 (p : Point) (hp : p∈IntegerCarrier rev90_planes)
    (hx0 : rev90_s0_ll.real.1≤p.1) (hx1 : p.1≤rev90_s0_lr.real.1) :
    p∈rationalHull (fractionRow90.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev90_plane73 rev90_plane53 rev90_s0_ll rev90_s0_lr rev90_s0_ul rev90_s0_ur
    (by decide) rev90_s0_ll_mem rev90_s0_lr_mem rev90_s0_ul_mem rev90_s0_ur_mem p
    (hp _ rev90_plane73_mem) (hp _ rev90_plane53_mem) hx0 hx1
def rev90_s1_ll : FractionPoint := ⟨42200335709617487,58446316538000000,27062046846878853,58446316538000000⟩
theorem rev90_s1_ll_mem : rev90_s1_ll.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane77 rev90_vertex5 rev90_vertex0 rev90_s1_ll
    rev90_vertex5_mem rev90_vertex0_mem (by decide)
def rev90_s1_lr : FractionPoint := ⟨37488082241261273,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev90_s1_lr_mem : rev90_s1_lr.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane77 rev90_vertex5 rev90_vertex0 rev90_s1_lr
    rev90_vertex5_mem rev90_vertex0_mem (by decide)
def rev90_s1_ul : FractionPoint := ⟨42200335709617487,58446316538000000,31384269691121147,58446316538000000⟩
theorem rev90_s1_ul_mem : rev90_s1_ul.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane57 rev90_vertex3 rev90_vertex2 rev90_s1_ul
    rev90_vertex3_mem rev90_vertex2_mem (by decide)
def rev90_s1_ur : FractionPoint := ⟨37488082241261273,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev90_s1_ur_mem : rev90_s1_ur.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane57 rev90_vertex3 rev90_vertex2 rev90_s1_ur
    rev90_vertex3_mem rev90_vertex2_mem (by decide)
theorem rev90_slab1 (p : Point) (hp : p∈IntegerCarrier rev90_planes)
    (hx0 : rev90_s1_ll.real.1≤p.1) (hx1 : p.1≤rev90_s1_lr.real.1) :
    p∈rationalHull (fractionRow90.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev90_plane77 rev90_plane57 rev90_s1_ll rev90_s1_lr rev90_s1_ul rev90_s1_ur
    (by decide) rev90_s1_ll_mem rev90_s1_lr_mem rev90_s1_ul_mem rev90_s1_ur_mem p
    (hp _ rev90_plane77_mem) (hp _ rev90_plane57_mem) hx0 hx1
def rev90_s2_ll : FractionPoint := ⟨37488082241261273,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev90_s2_ll_mem : rev90_s2_ll.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane28 rev90_vertex0 rev90_vertex1 rev90_s2_ll
    rev90_vertex0_mem rev90_vertex1_mem (by decide)
def rev90_s2_lr : FractionPoint := ⟨11215758841,14536250000,1,2⟩
theorem rev90_s2_lr_mem : rev90_s2_lr.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane28 rev90_vertex0 rev90_vertex1 rev90_s2_lr
    rev90_vertex0_mem rev90_vertex1_mem (by decide)
def rev90_s2_ul : FractionPoint := ⟨37488082241261273,48928332174000000,8279959610234849,16309444058000000⟩
theorem rev90_s2_ul_mem : rev90_s2_ul.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane15 rev90_vertex2 rev90_vertex1 rev90_s2_ul
    rev90_vertex2_mem rev90_vertex1_mem (by decide)
def rev90_s2_ur : FractionPoint := ⟨11215758841,14536250000,1,2⟩
theorem rev90_s2_ur_mem : rev90_s2_ur.real ∈ rationalHull (fractionRow90.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow90 rev90_plane15 rev90_vertex2 rev90_vertex1 rev90_s2_ur
    rev90_vertex2_mem rev90_vertex1_mem (by decide)
theorem rev90_slab2 (p : Point) (hp : p∈IntegerCarrier rev90_planes)
    (hx0 : rev90_s2_ll.real.1≤p.1) (hx1 : p.1≤rev90_s2_lr.real.1) :
    p∈rationalHull (fractionRow90.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev90_plane28 rev90_plane15 rev90_s2_ll rev90_s2_lr rev90_s2_ul rev90_s2_ur
    (by decide) rev90_s2_ll_mem rev90_s2_lr_mem rev90_s2_ul_mem rev90_s2_ur_mem p
    (hp _ rev90_plane28_mem) (hp _ rev90_plane15_mem) hx0 hx1
theorem rev90_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev90_planes) : rev90_s0_ll.real.1≤p.1 := by
  have hc := rev90_plane53.combine_sound rev90_plane73 2112812000000 2112812000000 (by decide) (by decide) p
    (hp _ rev90_plane53_mem) (hp _ rev90_plane73_mem)
  exact (rev90_plane53.combine rev90_plane73 2112812000000 2112812000000).xBoundCheck_sound rev90_s0_ll.nx rev90_s0_ll.dx true (by decide) p hc
theorem rev90_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev90_planes) : p.1≤rev90_s2_lr.real.1 := by
  have hc := rev90_plane15.combine_sound rev90_plane28 1468788000000 1468788000000 (by decide) (by decide) p
    (hp _ rev90_plane15_mem) (hp _ rev90_plane28_mem)
  exact (rev90_plane15.combine rev90_plane28 1468788000000 1468788000000).xBoundCheck_sound rev90_s2_lr.nx rev90_s2_lr.dx false (by decide) p hc
theorem rev90_hull (p : Point) (hp : p∈IntegerCarrier rev90_planes) :
    p∈rationalHull (fractionRow90.map FractionPoint.rational) := by
  have hxlo := rev90_bound0_lo p hp
  have hxhi := rev90_bound0_hi p hp
  by_cases h0 : p.1≤rev90_s0_lr.real.1
  · exact rev90_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev90_s1_lr.real.1
  · exact rev90_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev90_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull90 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,9,10,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow90 := by
  rw [← fractionRow90_correct]
  exact rev90_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull90
