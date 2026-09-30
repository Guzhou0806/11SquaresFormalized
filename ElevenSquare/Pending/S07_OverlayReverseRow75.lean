import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks9
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev75_planes : List IntegerPlane := integerOverlayPlanes ![6,4,10,10]
def rev75_plane15 : IntegerPlane := ⟨2093220000000,1468788000000,2349463273104⟩
theorem rev75_plane15_mem : rev75_plane15 ∈ rev75_planes := by decide
def rev75_plane33 : IntegerPlane := ⟨(-2093220000000),1468788000000,(-880675273104)⟩
theorem rev75_plane33_mem : rev75_plane33 ∈ rev75_planes := by decide
def rev75_plane77 : IntegerPlane := ⟨1393416000000,(-2099728000000),33871860516⟩
theorem rev75_plane77_mem : rev75_plane77 ∈ rev75_planes := by decide
def rev75_vertex0 : FractionPoint := fractionRow75[0]!
theorem rev75_vertex0_mem : rev75_vertex0∈fractionRow75 := by decide
def rev75_vertex1 : FractionPoint := fractionRow75[1]!
theorem rev75_vertex1_mem : rev75_vertex1∈fractionRow75 := by decide
def rev75_vertex2 : FractionPoint := fractionRow75[2]!
theorem rev75_vertex2_mem : rev75_vertex2∈fractionRow75 := by decide
def rev75_s0_ll : FractionPoint := ⟨37488082241261273,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev75_s0_ll_mem : rev75_s0_ll.real ∈ rationalHull (fractionRow75.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow75 rev75_plane77 rev75_vertex2 rev75_vertex0 rev75_s0_ll
    rev75_vertex2_mem rev75_vertex0_mem (by decide)
def rev75_s0_lr : FractionPoint := ⟨11215758841,14536250000,15135847988765151,30522171140000000⟩
theorem rev75_s0_lr_mem : rev75_s0_lr.real ∈ rationalHull (fractionRow75.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow75 rev75_plane77 rev75_vertex2 rev75_vertex0 rev75_s0_lr
    rev75_vertex2_mem rev75_vertex0_mem (by decide)
def rev75_s0_ul : FractionPoint := ⟨37488082241261273,48928332174000000,8029484447765151,16309444058000000⟩
theorem rev75_s0_ul_mem : rev75_s0_ul.real ∈ rationalHull (fractionRow75.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow75 rev75_plane33 rev75_vertex2 rev75_vertex1 rev75_s0_ul
    rev75_vertex2_mem rev75_vertex1_mem (by decide)
def rev75_s0_ur : FractionPoint := ⟨11215758841,14536250000,1,2⟩
theorem rev75_s0_ur_mem : rev75_s0_ur.real ∈ rationalHull (fractionRow75.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow75 rev75_plane33 rev75_vertex2 rev75_vertex1 rev75_s0_ur
    rev75_vertex2_mem rev75_vertex1_mem (by decide)
theorem rev75_slab0 (p : Point) (hp : p∈IntegerCarrier rev75_planes)
    (hx0 : rev75_s0_ll.real.1≤p.1) (hx1 : p.1≤rev75_s0_lr.real.1) :
    p∈rationalHull (fractionRow75.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev75_plane77 rev75_plane33 rev75_s0_ll rev75_s0_lr rev75_s0_ul rev75_s0_ur
    (by decide) rev75_s0_ll_mem rev75_s0_lr_mem rev75_s0_ul_mem rev75_s0_ur_mem p
    (hp _ rev75_plane77_mem) (hp _ rev75_plane33_mem) hx0 hx1
def rev75_s1_ll : FractionPoint := ⟨11215758841,14536250000,15135847988765151,30522171140000000⟩
theorem rev75_s1_ll_mem : rev75_s1_ll.real ∈ rationalHull (fractionRow75.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow75 rev75_plane77 rev75_vertex2 rev75_vertex0 rev75_s1_ll
    rev75_vertex2_mem rev75_vertex0_mem (by decide)
def rev75_s1_lr : FractionPoint := ⟨20762435007382043,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev75_s1_lr_mem : rev75_s1_lr.real ∈ rationalHull (fractionRow75.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow75 rev75_plane77 rev75_vertex2 rev75_vertex0 rev75_s1_lr
    rev75_vertex2_mem rev75_vertex0_mem (by decide)
def rev75_s1_ul : FractionPoint := ⟨11215758841,14536250000,1,2⟩
theorem rev75_s1_ul_mem : rev75_s1_ul.real ∈ rationalHull (fractionRow75.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow75 rev75_plane15 rev75_vertex1 rev75_vertex0 rev75_s1_ul
    rev75_vertex1_mem rev75_vertex0_mem (by decide)
def rev75_s1_ur : FractionPoint := ⟨20762435007382043,26840938933200000,22242211529765151,44734898222000000⟩
theorem rev75_s1_ur_mem : rev75_s1_ur.real ∈ rationalHull (fractionRow75.map FractionPoint.rational) :=
  edgePointCheck_hull fractionRow75 rev75_plane15 rev75_vertex1 rev75_vertex0 rev75_s1_ur
    rev75_vertex1_mem rev75_vertex0_mem (by decide)
theorem rev75_slab1 (p : Point) (hp : p∈IntegerCarrier rev75_planes)
    (hx0 : rev75_s1_ll.real.1≤p.1) (hx1 : p.1≤rev75_s1_lr.real.1) :
    p∈rationalHull (fractionRow75.map FractionPoint.rational) :=
  slabCheck_sound (convex_convexHull ℝ _) rev75_plane77 rev75_plane15 rev75_s1_ll rev75_s1_lr rev75_s1_ul rev75_s1_ur
    (by decide) rev75_s1_ll_mem rev75_s1_lr_mem rev75_s1_ul_mem rev75_s1_ur_mem p
    (hp _ rev75_plane77_mem) (hp _ rev75_plane15_mem) hx0 hx1
theorem rev75_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev75_planes) : rev75_s0_ll.real.1≤p.1 := by
  have hc := rev75_plane33.combine_sound rev75_plane77 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev75_plane33_mem) (hp _ rev75_plane77_mem)
  exact (rev75_plane33.combine rev75_plane77 2099728000000 1468788000000).xBoundCheck_sound rev75_s0_ll.nx rev75_s0_ll.dx true (by decide) p hc
theorem rev75_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev75_planes) : p.1≤rev75_s1_lr.real.1 := by
  have hc := rev75_plane15.combine_sound rev75_plane77 2099728000000 1468788000000 (by decide) (by decide) p
    (hp _ rev75_plane15_mem) (hp _ rev75_plane77_mem)
  exact (rev75_plane15.combine rev75_plane77 2099728000000 1468788000000).xBoundCheck_sound rev75_s1_lr.nx rev75_s1_lr.dx false (by decide) p hc
theorem rev75_hull (p : Point) (hp : p∈IntegerCarrier rev75_planes) :
    p∈rationalHull (fractionRow75.map FractionPoint.rational) := by
  have hxlo := rev75_bound0_lo p hp
  have hxhi := rev75_bound0_hi p hp
  by_cases h0 : p.1≤rev75_s0_lr.real.1
  · exact rev75_slab0 p hp hxlo h0
  exact rev75_slab1 p hp (le_of_lt (lt_of_not_ge h0)) hxhi
theorem overlay_in_hull75 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,4,10,10] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow75 := by
  rw [← fractionRow75_correct]
  exact rev75_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull75
