import ElevenSquare.Pending.S07_Assignment
import ElevenSquare.Pending.S07_EncodedInitial
import ElevenSquare.Pending.S07_EncodedMasks
import ElevenSquare.Pending.S07_EncodedSemantics

/-! Map the original finite packing constraints into the relaxed search model.
The inverse is used only on occupied first-view cells, so no arbitrary choice
outside its image affects the witness. -/
namespace ElevenSquare.Pending.EncodedSearch
noncomputable section
open Propagation

theorem target_digits (a b c : Fin 6) :
    36*a.val+6*b.val+c.val < 216 ∧
    (36*a.val+6*b.val+c.val)/36 = a.val ∧
    ((36*a.val+6*b.val+c.val)/6)%6 = b.val ∧
    (36*a.val+6*b.val+c.val)%6 = c.val := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  omega

theorem supports_of_masks (a b c : Fin 6) (r : Fin 220)
    (h1 : label r.val 1 ∈ mask a.val)
    (h2 : label r.val 2 ∈ mask b.val)
    (h3 : label r.val 3 ∈ mask c.val) :
    supports (36*a.val+6*b.val+c.val) r.val = true := by
  obtain ⟨_, ha, hb, hc⟩ := target_digits a b c
  simp only [supports, ha, hb, hc, List.contains, List.elem_eq_mem]
  simp [h1, h2, h3]

theorem initial_mem {k v : ℕ} {options : List ℕ}
    (h : (v,options) ∈ initialDomains k) :
    v ∈ mask k ∧ options = (List.range 220).filter (fun r => decide (label r 0 = v)) := by
  obtain ⟨u, hu, he⟩ := List.mem_map.mp h
  have huv : u = v := congrArg Prod.fst he
  subst u
  exact ⟨hu, (congrArg Prod.snd he).symm⟩

theorem avoiding_encoded (f : Owner → Fin 220) (hf : AvoidingAssignment f) :
    ∃ k : Fin 6, Sat compatible supports (initialDomains k.val) (List.range 216) := by
  classical
  let M := fun g : Fin 4 => Finset.univ.image (fun i => overlayLabels (f i) g)
  obtain ⟨k0, hk0⟩ := other_mask_rep (M 0) (hf.2.1 0)
  obtain ⟨k1, hk1⟩ := other_mask_rep (M 1) (hf.2.1 1)
  obtain ⟨k2, hk2⟩ := other_mask_rep (M 2) (hf.2.1 2)
  obtain ⟨k3, hk3⟩ := other_mask_rep (M 3) (hf.2.1 3)
  let first := fun i : Owner => (overlayLabels (f i) 0).val
  let owner := Function.invFun first
  have howner (v : ℕ) (hv : v ∈ mask k0.val) : first (owner v) = v := by
    apply Function.invFun_eq
    have hv16 := mask_bounded k0 v hv
    have hm : (⟨v,hv16⟩ : Fin 16) ∈ M 0 := (hk0 ⟨v,hv16⟩).mpr hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    exact ⟨i, congrArg Fin.val hi⟩
  have hmem (g : Fin 4) (i : Owner) : overlayLabels (f i) g ∈ M g :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let assignment := fun v => (f (owner v)).val
  let t := 36*k1.val+6*k2.val+k3.val
  refine ⟨k0, assignment, t, List.mem_range.mpr (target_digits k1 k2 k3).1, ?_, ?_⟩
  · intro v options hv
    obtain ⟨hvMask, rfl⟩ := initial_mem hv
    refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (f (owner v)).isLt, ?_⟩, ?_⟩
    · apply decide_eq_true
      exact (labels_correct (f (owner v)) 0).trans (howner v hvMask)
    · apply supports_of_masks k1 k2 k3 (f (owner v))
      · rw [show label (assignment v) 1 = (overlayLabels (f (owner v)) 1).val from labels_correct _ 1]
        exact (hk1 _).mp (hmem 1 (owner v))
      · rw [show label (assignment v) 2 = (overlayLabels (f (owner v)) 2).val from labels_correct _ 2]
        exact (hk2 _).mp (hmem 2 (owner v))
      · rw [show label (assignment v) 3 = (overlayLabels (f (owner v)) 3).val from labels_correct _ 3]
        exact (hk3 _).mp (hmem 3 (owner v))
  · intro u left hu v right hv hne
    have huv : owner u ≠ owner v := by
      intro he
      apply hne
      exact (howner u (initial_mem hu).1).symm.trans
        ((congrArg first he).trans (howner v (initial_mem hv).1))
    apply compatible_of_original (f (owner u)) (f (owner v))
    · intro g he
      exact huv (hf.1 g he)
    · exact hf.2.2 _ _ huv

end
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.avoiding_encoded
