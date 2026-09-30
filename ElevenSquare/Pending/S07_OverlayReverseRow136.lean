import ElevenSquare.Pending.S07_IntegerBounds
import ElevenSquare.Pending.S07_SlabCertificate
import ElevenSquare.Pending.S07_OverlayVertexChecks17
namespace ElevenSquare.Pending.OverlayVertexChecks
def rev136_planes : List IntegerPlane := integerOverlayPlanes ![9,9,6,6]
def rev136_plane10 : IntegerPlane := ⟨2164112000000,(-1343640000000),410236000000⟩
theorem rev136_plane10_mem : rev136_plane10 ∈ rev136_planes := by decide
def rev136_plane30 : IntegerPlane := ⟨(-2164112000000),(-1343640000000),(-1753876000000)⟩
theorem rev136_plane30_mem : rev136_plane30 ∈ rev136_planes := by decide
def rev136_plane53 : IntegerPlane := ⟨1343640000000,2164112000000,1753876000000⟩
theorem rev136_plane53_mem : rev136_plane53 ∈ rev136_planes := by decide
def rev136_vertex0 : FractionPoint := fractionRow136[0]!
theorem rev136_vertex0_mem : rev136_vertex0∈fractionRow136 := by decide
theorem rev136_bound0_lo (p : Point) (hp : p∈IntegerCarrier rev136_planes) : rev136_vertex0.real.1≤p.1 := by
  have hc := rev136_plane30.combine_sound rev136_plane53 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev136_plane30_mem) (hp _ rev136_plane53_mem)
  exact (rev136_plane30.combine rev136_plane53 2164112000000 1343640000000).xBoundCheck_sound rev136_vertex0.nx rev136_vertex0.dx true (by decide) p hc
theorem rev136_bound0_hi (p : Point) (hp : p∈IntegerCarrier rev136_planes) : p.1≤rev136_vertex0.real.1 := by
  have hc := rev136_plane10.combine_sound rev136_plane53 2164112000000 1343640000000 (by decide) (by decide) p
    (hp _ rev136_plane10_mem) (hp _ rev136_plane53_mem)
  exact (rev136_plane10.combine rev136_plane53 2164112000000 1343640000000).xBoundCheck_sound rev136_vertex0.nx rev136_vertex0.dx false (by decide) p hc
theorem rev136_bound1_lo (p : Point) (hp : p∈IntegerCarrier rev136_planes) : rev136_vertex0.real.2≤p.2 := by
  have hc := rev136_plane10.combine_sound rev136_plane30 2164112000000 2164112000000 (by decide) (by decide) p
    (hp _ rev136_plane10_mem) (hp _ rev136_plane30_mem)
  exact (rev136_plane10.combine rev136_plane30 2164112000000 2164112000000).swap.xBoundCheck_sound rev136_vertex0.ny rev136_vertex0.dy true (by decide) (p.2,p.1)
    ((rev136_plane10.combine rev136_plane30 2164112000000 2164112000000).swap_contains p hc)
theorem rev136_bound1_hi (p : Point) (hp : p∈IntegerCarrier rev136_planes) : p.2≤rev136_vertex0.real.2 := by
  have hc := rev136_plane30.combine_sound rev136_plane53 1343640000000 2164112000000 (by decide) (by decide) p
    (hp _ rev136_plane30_mem) (hp _ rev136_plane53_mem)
  exact (rev136_plane30.combine rev136_plane53 1343640000000 2164112000000).swap.xBoundCheck_sound rev136_vertex0.ny rev136_vertex0.dy false (by decide) (p.2,p.1)
    ((rev136_plane30.combine rev136_plane53 1343640000000 2164112000000).swap_contains p hc)
theorem rev136_hull (p : Point) (hp : p∈IntegerCarrier rev136_planes) :
    p∈rationalHull (fractionRow136.map FractionPoint.rational) := by
  have hxlo := rev136_bound0_lo p hp
  have hxhi := rev136_bound0_hi p hp
  have hylo := rev136_bound1_lo p hp
  have hyhi := rev136_bound1_hi p hp
  have he : p=rev136_vertex0.real := Prod.ext (le_antisymm hxhi hxlo) (le_antisymm hyhi hylo)
  rw [he]
  exact rev136_vertex0.mem_rationalHull fractionRow136 rev136_vertex0_mem
theorem overlay_in_hull136 (p : Point)
    (hp : ∀ g, ClosedCell ((![9,9,6,6] : Fin 4 → Fin 16) g) (view g p)) :
    p∈rationalHull GridDistance.rationalRow136 := by
  rw [← fractionRow136_correct]
  exact rev136_hull p ((integerOverlayPlanes_correct _ p).mpr hp)
end ElevenSquare.Pending.OverlayVertexChecks
#print axioms ElevenSquare.Pending.OverlayVertexChecks.overlay_in_hull136
