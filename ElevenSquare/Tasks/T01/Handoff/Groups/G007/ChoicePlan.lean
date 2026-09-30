import ElevenSquare.Tasks.T01.Handoff.PlanAPI.MixedFeature
import ElevenSquare.Tasks.T01.Handoff.Groups.G007.Capacity

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G007
open ElevenSquare.Pending ElevenSquare.Tasks.T01 ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

/-- A checked row choice and its independently owned blocking points. -/
structure ChoiceRowCertificate where
  row : PoseRow
  blocks : List OwnedBlock
  choice : ∀ q : UnitSquare, row.contains q →
    (∀ p ∈ blocks.map OwnedBlock.point, ¬ OpenSquare q (realPoint p)) →
    OpenSquare q (realPoint point) ∨ BaselineMajorityCapture sites 2 q

def ChoiceRowCertificate.Check (s : PoseState) (i : Owner)
    (c : ChoiceRowCertificate) : Prop :=
  c.blocks.Forall (fun b => b.Check s i)

theorem ChoiceRowCertificate.sound {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (hs : StateHolds P s) (i : Owner)
    (c : ChoiceRowCertificate) (hc : c.Check s i)
    (hr : c.row.contains (P.squares i)) :
    OpenSquare (P.squares i) (realPoint point) ∨
      BaselineMajorityCapture sites 2 (P.squares i) := by
  apply c.choice _ hr
  intro p hp hinside
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
  have hcheck : b.Check s i := (List.forall_iff_forall_mem).mp hc b hb
  have hmember : realPoint b.point ∈ rationalHull (s.owned b.partner) := by
    rw [← hcheck.2.2]
    exact hullWitness_sound (s.owned b.partner) b.witness hcheck.2.1
  exact P.interior_disjoint i b.partner hcheck.1 (realPoint b.point)
    ⟨hinside, hs.2 b.partner hmember⟩

structure ChoiceThreePlan where
  owners : Fin 3 → Owner
  rows : Fin 3 → List ChoiceRowCertificate

def ChoiceThreePlan.Check (s : PoseState) (c : ChoiceThreePlan) : Prop :=
  Function.Injective c.owners ∧
  ∀ j : Fin 3,
    (c.rows j).map ChoiceRowCertificate.row = s.rows (c.owners j) ∧
    ∀ cert ∈ c.rows j, cert.Check s (c.owners j)

theorem choice_three_plan_refutes {S : ℝ} (P : Packing 11 S)
    (s : PoseState) (c : ChoiceThreePlan) (hc : c.Check s)
    (hs : StateHolds P s) : False := by
  apply three_captures_impossible P c.owners hc.1
  intro j
  obtain ⟨r, hr, hq⟩ := hs.1 (c.owners j)
  rw [← (hc.2 j).1] at hr
  obtain ⟨cert, hcert, rfl⟩ := List.mem_map.mp hr
  exact cert.sound P s hs (c.owners j) ((hc.2 j).2 cert hcert) hq

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G007

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.choice_three_plan_refutes
