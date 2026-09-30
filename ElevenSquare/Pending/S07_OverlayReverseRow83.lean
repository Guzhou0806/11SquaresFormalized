import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks10
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev83_planes : List IntegerPlane := integerOverlayPlanes ![6,6,9,9]
def rev83_plane13 : IntegerPlane := ⟨(-2164112000000),1343640000000,(-410236000000)⟩
theorem rev83_plane13_mem : rev83_plane13 ∈ rev83_planes := by decide
def rev83_plane33 : IntegerPlane := ⟨2164112000000,1343640000000,1753876000000⟩
theorem rev83_plane33_mem : rev83_plane33 ∈ rev83_planes := by decide
def rev83_plane50 : IntegerPlane := ⟨(-1343640000000),(-2164112000000),(-1753876000000)⟩
theorem rev83_plane50_mem : rev83_plane50 ∈ rev83_planes := by decide
def rev83_vertex0 : FractionPoint := fractionRow83[0]!
theorem rev83_vertex0_mem : rev83_vertex0∈fractionRow83 := by decide
theorem rev83_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev83_planes) : rev83_vertex0.real.1≤p.1 := by
  have hc := rev83_plane13.combine_sound rev83_plane50 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev83_plane13_mem) (hp _ rev83_plane50_mem)
  exact (rev83_plane13.combine rev83_plane50 2164112000000 1343640000000).xBoundCheck_sound rev83_vertex0.nx rev83_vertex0.dx true (by decide) p hc
theorem rev83_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev83_planes) : p.1≤rev83_vertex0.real.1 := by
  have hc := rev83_plane33.combine_sound rev83_plane50 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev83_plane33_mem) (hp _ rev83_plane50_mem)
  exact (rev83_plane33.combine rev83_plane50 2164112000000 1343640000000).xBoundCheck_sound rev83_vertex0.nx rev83_vertex0.dx false (by decide) p hc
theorem rev83_bound1_lo (p : Point) (hp : p∈IntegerCarrier rev83_planes) : rev83_vertex0.real.2≤p.2 := by
  have hc := rev83_plane33.combine_sound rev83_plane50 1343640000000 2164112000000 (by decide) (by decide) p
    (hp _ rev83_plane33_mem) (hp _ rev83_plane50_mem)
  exact (rev83_plane33.combine rev83_plane50 1343640000000 2164112000000).swap.xBoundCheck_sound rev83_vertex0.ny rev83_vertex0.dy true (by decide) (p.2,p.1)
    ((rev83_plane33.combine rev83_plane50 1343640000000 2164112000000).swap_contains p hc)
theorem rev83_bound1_hi (p : Point) (hp : p∈IntegerCarrier rev83_planes) : p.2≤rev83_vertex0.real.2 := by
  have hc := rev83_plane13.combine_sound rev83_plane33 2164112000000 2164112000000 (by decide) (by decide) p
    (hp _ rev83_plane13_mem) (hp _ rev83_plane33_mem)
  exact (rev83_plane13.combine rev83_plane33 2164112000000 2164112000000).swap.xBoundCheck_sound rev83_vertex0.ny rev83_vertex0.dy false (by decide) (p.2,p.1)
    ((rev83_plane13.combine rev83_plane33 2164112000000 2164112000000).swap_contains p hc)
theorem rev83_hull (p : Point) (hp : p∈IntegerCarrier rev83_planes) :
    p∈rationalHull (fractionRow83.map FractionPoint.rational) := by
  have hxlo := rev83_bound0_lo p hp
  have hxhi := rev83_bound0_hi p hp
  have hylo := rev83_bound1_lo p hp
  have hyhi := rev83_bound1_hi p hp
  have he : p=rev83_vertex0.real := Prod.ext (le_antisymm hxhi hxlo) (le_antisymm hyhi hylo)
  rw [he]
  exact rev83_vertex0.mem_rationalHull fractionRow83 rev83_vertex0_mem
theorem overlay_in_hull83 (p : Point)
    (hp : ∀ g, ClosedCell ((![6,6,9,9] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow83 := by
  rw [← fractionRow83_correct]
  exact rev83_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull83
