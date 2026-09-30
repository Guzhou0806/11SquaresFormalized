import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks10
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev82_planes : List IntegerPlane := integerOverlayPlanes ![6,6,9,6]
def rev82_plane13 : IntegerPlane := ⟨(-2164112000000),1343640000000,(-410236000000)⟩
theorem rev82_plane13_mem : rev82_plane13 ∈ rev82_planes := by decide
def rev82_plane33 : IntegerPlane := ⟨2164112000000,1343640000000,1753876000000⟩
theorem rev82_plane33_mem : rev82_plane33 ∈ rev82_planes := by decide
def rev82_plane50 : IntegerPlane := ⟨(-1343640000000),(-2164112000000),(-1753876000000)⟩
theorem rev82_plane50_mem : rev82_plane50 ∈ rev82_planes := by decide
def rev82_plane73 : IntegerPlane := ⟨1343640000000,(-2164112000000),(-410236000000)⟩
theorem rev82_plane73_mem : rev82_plane73 ∈ rev82_planes := by decide
def rev82_vertex0 : FractionPoint := fractionRow82[0]!
theorem rev82_vertex0_mem : rev82_vertex0∈fractionRow82 := by decide
theorem rev82_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev82_planes) : rev82_vertex0.real.1≤p.1 := by
  have hc := rev82_plane13.combine_sound rev82_plane50 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev82_plane13_mem) (hp _ rev82_plane50_mem)
  exact (rev82_plane13.combine rev82_plane50 2164112000000 1343640000000).xBoundCheck_sound rev82_vertex0.nx rev82_vertex0.dx true (by decide) p hc
theorem rev82_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev82_planes) : p.1≤rev82_vertex0.real.1 := by
  have hc := rev82_plane33.combine_sound rev82_plane50 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev82_plane33_mem) (hp _ rev82_plane50_mem)
  exact (rev82_plane33.combine rev82_plane50 2164112000000 1343640000000).xBoundCheck_sound rev82_vertex0.nx rev82_vertex0.dx false (by decide) p hc
theorem rev82_bound1_lo (p : Point) (hp : p∈IntegerCarrier rev82_planes) : rev82_vertex0.real.2≤p.2 := by
  have hc := rev82_plane13.combine_sound rev82_plane73 1343640000000 2164112000000 (by decide) (by decide) p
    (hp _ rev82_plane13_mem) (hp _ rev82_plane73_mem)
  exact (rev82_plane13.combine rev82_plane73 1343640000000 2164112000000).swap.xBoundCheck_sound rev82_vertex0.ny rev82_vertex0.dy true (by decide) (p.2,p.1)
    ((rev82_plane13.combine rev82_plane73 1343640000000 2164112000000).swap_contains p hc)
theorem rev82_bound1_hi (p : Point) (hp : p∈IntegerCarrier rev82_planes) : p.2≤rev82_vertex0.real.2 := by
  have hc := rev82_plane13.combine_sound rev82_plane33 2164112000000 2164112000000 (by decide) (by decide) p
    (hp _ rev82_plane13_mem) (hp _ rev82_plane33_mem)
  exact (rev82_plane13.combine rev82_plane33 2164112000000 2164112000000).swap.xBoundCheck_sound rev82_vertex0.ny rev82_vertex0.dy false (by decide) (p.2,p.1)
    ((rev82_plane13.combine rev82_plane33 2164112000000 2164112000000).swap_contains p hc)
theorem rev82_hull (p : Point) (hp : p∈IntegerCarrier rev82_planes) :
    p∈rationalHull (fractionRow82.map FractionPoint.rational) := by
  have hxlo := rev82_bound0_lo p hp
  have hxhi := rev82_bound0_hi p hp
  have hylo := rev82_bound1_lo p hp
  have hyhi := rev82_bound1_hi p hp
  have he : p=rev82_vertex0.real := Prod.ext (le_antisymm hxhi hxlo) (le_antisymm hyhi hylo)
  rw [he]
  exact rev82_vertex0.mem_rationalHull fractionRow82 rev82_vertex0_mem
theorem overlay_in_hull82 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,6,9,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow82 := by
  rw [← fractionRow82_correct]
  exact rev82_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull82
