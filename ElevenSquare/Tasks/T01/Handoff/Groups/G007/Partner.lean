import ElevenSquare.Tasks.T01.Root

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- The owner assigned to a physical cell in the root's canonical order. -/
def partner (m : Finset (Fin 16)) (cell : Fin 16) : Owner :=
  if h : ∃ i : Owner, baselineRoles m i = cell then Classical.choose h else 0

theorem partner_spec {m : Finset (Fin 16)} (hm : m.card = 11)
    {cell : Fin 16} (hc : cell ∈ m) :
    baselineRoles m (partner m cell) = cell := by
  have hex : ∃ i : Owner, baselineRoles m i = cell := by
    have hi : cell ∈ Finset.univ.image (baselineRoles m) := by
      rwa [baselineRoles_image hm]
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hi
    exact ⟨i, he⟩
  unfold partner
  simp only [dif_pos hex]
  exact Classical.choose_spec hex

theorem partner_ne {m : Finset (Fin 16)} (hm : m.card = 11)
    {cell other : Fin 16} (hc : cell ∈ m) (ho : other ∈ m)
    (hne : cell ≠ other) : partner m cell ≠ partner m other := by
  intro he
  apply hne
  calc
    cell = baselineRoles m (partner m cell) := (partner_spec hm hc).symm
    _ = baselineRoles m (partner m other) := congrArg (baselineRoles m) he
    _ = other := partner_spec hm ho

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.partner_ne
