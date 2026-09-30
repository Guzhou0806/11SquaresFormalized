import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks10
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev86_planes : List IntegerPlane := integerOverlayPlanes ![6,9,9,6]
def rev86_plane13 : IntegerPlane := ⟨(-2164112000000),1343640000000,(-410236000000)⟩
theorem rev86_plane13_mem : rev86_plane13 ∈ rev86_planes := by decide
def rev86_plane14 : IntegerPlane := ⟨(-51300000000),2168356000000,1163521164456⟩
theorem rev86_plane14_mem : rev86_plane14 ∈ rev86_planes := by decide
def rev86_plane30 : IntegerPlane := ⟨(-2164112000000),(-1343640000000),(-1753876000000)⟩
theorem rev86_plane30_mem : rev86_plane30 ∈ rev86_planes := by decide
def rev86_plane73 : IntegerPlane := ⟨1343640000000,(-2164112000000),(-410236000000)⟩
theorem rev86_plane73_mem : rev86_plane73 ∈ rev86_planes := by decide
def rev86_plane74 : IntegerPlane := ⟨2168356000000,(-51300000000),1163521164456⟩
theorem rev86_plane74_mem : rev86_plane74 ∈ rev86_planes := by decide
def rev86_vertex0 : FractionPoint := fractionRow86[0]!
theorem rev86_vertex0_mem : rev86_vertex0∈fractionRow86 := by decide
def rev86_vertex1 : FractionPoint := fractionRow86[1]!
theorem rev86_vertex1_mem : rev86_vertex1∈fractionRow86 := by decide
def rev86_vertex2 : FractionPoint := fractionRow86[2]!
theorem rev86_vertex2_mem : rev86_vertex2∈fractionRow86 := by decide
def rev86_vertex3 : FractionPoint := fractionRow86[3]!
theorem rev86_vertex3_mem : rev86_vertex3∈fractionRow86 := by decide
def rev86_s0_ll : FractionPoint := ⟨1,2,1,2⟩
theorem rev86_s0_ll_mem : rev86_s0_ll.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane73 rev86_vertex1 rev86_vertex2 rev86_s0_ll
    rev86_vertex1_mem rev86_vertex2_mem (by decide)
def rev86_s0_lr : FractionPoint := ⟨403436064050273,760466530900000,21351089521770030343,41143368627976520000⟩
theorem rev86_s0_lr_mem : rev86_s0_lr.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane73 rev86_vertex1 rev86_vertex2 rev86_s0_lr
    rev86_vertex1_mem rev86_vertex2_mem (by decide)
def rev86_s0_ul : FractionPoint := ⟨1,2,1,2⟩
theorem rev86_s0_ul_mem : rev86_s0_ul.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane13 rev86_vertex1 rev86_vertex0 rev86_s0_ul
    rev86_vertex1_mem rev86_vertex0_mem (by decide)
def rev86_s0_ur : FractionPoint := ⟨403436064050273,760466530900000,1044011192867271,1901166327250000⟩
theorem rev86_s0_ur_mem : rev86_s0_ur.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane13 rev86_vertex1 rev86_vertex0 rev86_s0_ur
    rev86_vertex1_mem rev86_vertex0_mem (by decide)
theorem rev86_slab0 (p : Point) (hp : p∈IntegerCarrier rev86_planes)
    (hx0 : rev86_s0_ll.real.1≤p.1) (hx1 : p.1≤rev86_s0_lr.real.1) :
    p∈rationalHull (fractionRow86.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev86_plane73 rev86_plane13 rev86_s0_ll rev86_s0_lr rev86_s0_ul rev86_s0_ur
    (by decide) rev86_s0_ll_mem rev86_s0_lr_mem rev86_s0_ul_mem rev86_s0_ur_mem p
    (hp _ rev86_plane73_mem) (hp _ rev86_plane13_mem) hx0 hx1
def rev86_s1_ll : FractionPoint := ⟨403436064050273,760466530900000,21351089521770030343,41143368627976520000⟩
theorem rev86_s1_ll_mem : rev86_s1_ll.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane73 rev86_vertex1 rev86_vertex2 rev86_s1_ll
    rev86_vertex1_mem rev86_vertex2_mem (by decide)
def rev86_s1_lr : FractionPoint := ⟨1044011192867271,1901166327250000,403436064050273,760466530900000⟩
theorem rev86_s1_lr_mem : rev86_s1_lr.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane73 rev86_vertex1 rev86_vertex2 rev86_s1_lr
    rev86_vertex1_mem rev86_vertex2_mem (by decide)
def rev86_s1_ul : FractionPoint := ⟨403436064050273,760466530900000,1044011192867271,1901166327250000⟩
theorem rev86_s1_ul_mem : rev86_s1_ul.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane14 rev86_vertex0 rev86_vertex3 rev86_s1_ul
    rev86_vertex0_mem rev86_vertex3_mem (by decide)
def rev86_s1_ur : FractionPoint := ⟨1044011192867271,1901166327250000,59621185081593362277,108484352965539500000⟩
theorem rev86_s1_ur_mem : rev86_s1_ur.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane14 rev86_vertex0 rev86_vertex3 rev86_s1_ur
    rev86_vertex0_mem rev86_vertex3_mem (by decide)
theorem rev86_slab1 (p : Point) (hp : p∈IntegerCarrier rev86_planes)
    (hx0 : rev86_s1_ll.real.1≤p.1) (hx1 : p.1≤rev86_s1_lr.real.1) :
    p∈rationalHull (fractionRow86.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev86_plane73 rev86_plane14 rev86_s1_ll rev86_s1_lr rev86_s1_ul rev86_s1_ur
    (by decide) rev86_s1_ll_mem rev86_s1_lr_mem rev86_s1_ul_mem rev86_s1_ur_mem p
    (hp _ rev86_plane73_mem) (hp _ rev86_plane14_mem) hx0 hx1
def rev86_s2_ll : FractionPoint := ⟨1044011192867271,1901166327250000,403436064050273,760466530900000⟩
theorem rev86_s2_ll_mem : rev86_s2_ll.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane74 rev86_vertex2 rev86_vertex3 rev86_s2_ll
    rev86_vertex2_mem rev86_vertex3_mem (by decide)
def rev86_s2_lr : FractionPoint := ⟨7654744503,13928000000,7654744503,13928000000⟩
theorem rev86_s2_lr_mem : rev86_s2_lr.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane74 rev86_vertex2 rev86_vertex3 rev86_s2_lr
    rev86_vertex2_mem rev86_vertex3_mem (by decide)
def rev86_s2_ul : FractionPoint := ⟨1044011192867271,1901166327250000,59621185081593362277,108484352965539500000⟩
theorem rev86_s2_ul_mem : rev86_s2_ul.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane14 rev86_vertex0 rev86_vertex3 rev86_s2_ul
    rev86_vertex0_mem rev86_vertex3_mem (by decide)
def rev86_s2_ur : FractionPoint := ⟨7654744503,13928000000,7654744503,13928000000⟩
theorem rev86_s2_ur_mem : rev86_s2_ur.real ∈ rationalHull (fractionRow86.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow86 rev86_plane14 rev86_vertex0 rev86_vertex3 rev86_s2_ur
    rev86_vertex0_mem rev86_vertex3_mem (by decide)
theorem rev86_slab2 (p : Point) (hp : p∈IntegerCarrier rev86_planes)
    (hx0 : rev86_s2_ll.real.1≤p.1) (hx1 : p.1≤rev86_s2_lr.real.1) :
    p∈rationalHull (fractionRow86.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev86_plane74 rev86_plane14 rev86_s2_ll rev86_s2_lr rev86_s2_ul rev86_s2_ur
    (by decide) rev86_s2_ll_mem rev86_s2_lr_mem rev86_s2_ul_mem rev86_s2_ur_mem p
    (hp _ rev86_plane74_mem) (hp _ rev86_plane14_mem) hx0 hx1
theorem rev86_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev86_planes) : rev86_s0_ll.real.1≤p.1 := by
  have hc := rev86_plane13.combine_sound rev86_plane30 1343640000000 1343640000000 (by decide) (by decide) p
    (hp _ rev86_plane13_mem) (hp _ rev86_plane30_mem)
  exact (rev86_plane13.combine rev86_plane30 1343640000000 1343640000000).xBoundCheck_sound rev86_s0_ll.nx rev86_s0_ll.dx true (by decide) p hc
theorem rev86_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev86_planes) : p.1≤rev86_s2_lr.real.1 := by
  have hc := rev86_plane14.combine_sound rev86_plane74 51300000000 2168356000000 (by decide) (by decide) p
    (hp _ rev86_plane14_mem) (hp _ rev86_plane74_mem)
  exact (rev86_plane14.combine rev86_plane74 51300000000 2168356000000).xBoundCheck_sound rev86_s2_lr.nx rev86_s2_lr.dx false (by decide) p hc
theorem rev86_hull (p : Point) (hp : p∈IntegerCarrier rev86_planes) :
    p∈rationalHull (fractionRow86.map FractionPoint.rational) := by
  have hxlo := rev86_bound0_lo p hp
  have hxhi := rev86_bound0_hi p hp
  by_cases h0 : p.1≤rev86_s0_lr.real.1
  · exact rev86_slab0 p hp hxlo h0
  by_cases h1 : p.1≤rev86_s1_lr.real.1
  · exact rev86_slab1 p hp (le_of_lt (lt_of_not_ge h0)) h1
  exact rev86_slab2 p hp (le_of_lt (lt_of_not_ge h1)) hxhi
theorem overlay_in_hull86 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,9,9,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow86 := by
  rw [← fractionRow86_correct]
  exact rev86_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull86
