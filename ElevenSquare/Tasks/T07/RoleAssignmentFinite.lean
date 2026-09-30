import ElevenSquare.Pending.Types
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-! Exact finite maps between ascending occupied-cell owners and construction roles. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def ownerCell : Owner → Fin 16 := ![0,1,2,3,4,8,9,10,11,13,15]

def roleCell : Owner → Fin 16 := ![3,15,8,0,4,1,2,11,9,10,13]

def roleOwner : Owner → Owner := ![3,10,5,0,4,1,2,8,6,7,9]

theorem ownerCell_injective : Function.Injective ownerCell := by decide

theorem roleCell_injective : Function.Injective roleCell := by decide

def ownerRole : Owner → Owner := ![3,5,6,0,4,2,8,9,7,10,1]

theorem roleOwner_left_inverse (i : Owner) : ownerRole (roleOwner i) = i := by
  fin_cases i <;> rfl

theorem roleOwner_right_inverse (i : Owner) : roleOwner (ownerRole i) = i := by
  fin_cases i <;> rfl

theorem roleOwner_bijective : Function.Bijective roleOwner := by
  constructor
  · intro i j h
    calc i = ownerRole (roleOwner i) := (roleOwner_left_inverse i).symm
      _ = ownerRole (roleOwner j) := congrArg ownerRole h
      _ = j := roleOwner_left_inverse j
  · intro i
    exact ⟨ownerRole i, roleOwner_right_inverse i⟩

def rolePermutation : Equiv.Perm Owner := Equiv.ofBijective roleOwner roleOwner_bijective

theorem role_cell_correspondence (i : Owner) : ownerCell (roleOwner i) = roleCell i := by
  fin_cases i <;> decide

theorem ownerCell_image :
    Finset.univ.image ownerCell = ({0,1,2,3,4,8,9,10,11,13,15} : Finset (Fin 16)) := by
  ext j
  fin_cases j <;> decide

theorem roleCell_image :
    Finset.univ.image roleCell = ({0,1,2,3,4,8,9,10,11,13,15} : Finset (Fin 16)) := by
  ext j
  fin_cases j <;> decide

/-- Equality of finite images supplies a genuine owner permutation, not an
arbitrary many-to-one assignment. -/
theorem image_permutation {β : Type} [DecidableEq β] (a b : Owner → β)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (him : Finset.univ.image a = Finset.univ.image b) :
    ∃ perm : Equiv.Perm Owner, ∀ i, a (perm i) = b i := by
  classical
  have hex (i : Owner) : ∃ j : Owner, a j = b i := by
    have hm : b i ∈ Finset.univ.image a := by
      rw [him]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact ⟨j, hj⟩
  choose f hf using hex
  have hfi : Function.Injective f := by
    intro i j hij
    apply hb
    rw [← hf i, ← hf j, hij]
  let perm : Equiv.Perm Owner := Equiv.ofBijective f
    ⟨hfi, Finite.surjective_of_injective hfi⟩
  exact ⟨perm, hf⟩

end
end ElevenSquare.Tasks.T07
