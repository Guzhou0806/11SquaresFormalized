import ElevenSquare.Tasks.T01.Handoff.Inventory

namespace ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff
set_option maxRecDepth 10000

def omittedGroups : List Group := [⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨87, by decide⟩]

def Selected (g : Group) : Prop := g ∉ omittedGroups
instance (g : Group) : Decidable (Selected g) := inferInstanceAs (Decidable (g ∉ omittedGroups))

theorem group_partition (g : Group) :
    Selected g ∨ g ∈ omittedGroups := by
  by_cases h : g ∈ omittedGroups
  · exact Or.inr h
  · exact Or.inl h

def Covered (g : Group) : Prop :=
  ∀ k ∈ groupCases g, ∃ h : Group, Selected h ∧ k ∈ groupCases h

theorem covered_of_assignments (g : Group) (a : List (ℕ × Group))
    (keys : a.map Prod.fst = groupCases g)
    (valid : a.Forall (fun p => Selected p.2 ∧ p.1 ∈ groupCases p.2)) :
    Covered g := by
  intro k hk
  rw [← keys] at hk
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hk
  have h := (List.forall_iff_forall_mem.mp valid) p hp
  exact ⟨p.2, h.1, heq ▸ h.2⟩

end ElevenSquare.Tasks.T01.Handoff.ReducedCoverage
