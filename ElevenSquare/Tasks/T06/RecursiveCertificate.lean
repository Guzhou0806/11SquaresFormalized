import ElevenSquare.Tasks.T06.DataIntegral

namespace ElevenSquare.Tasks.T06

/-- Direct structural summation of a finite vector, avoiding a finite-set
enumeration in the arithmetic certificate's kernel computation. -/
def certificateVectorSum {α : Type*} [Zero α] [Add α] :
    {n : ℕ} → (Fin n → α) → α
  | 0, _ => 0
  | n + 1, f => f 0 + certificateVectorSum (fun i : Fin n => f i.succ)

theorem sum_eq_certificateVectorSum {α : Type*} [AddCommMonoid α]
    (n : ℕ) (f : Fin n → α) :
    (∑ i, f i) = certificateVectorSum f := by
  induction n with
  | zero => simp [certificateVectorSum]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    change f 0 + (∑ i : Fin n, f i.succ) =
      f 0 + certificateVectorSum (fun i : Fin n => f i.succ)
    rw [ih]

theorem certificateVectorSum_vecCons {α : Type*} [Zero α] [Add α]
    {n : ℕ} (a : α) (v : Fin n → α) :
    certificateVectorSum (Matrix.vecCons a v) = a + certificateVectorSum v := rfl

theorem certificateVectorSum_vecEmpty {α : Type*} [Zero α] [Add α] :
    certificateVectorSum (Matrix.vecEmpty : Fin 0 → α) = 0 := rfl

theorem certificate_comp_vecCons {α β : Type*} {n : ℕ}
    (f : α → β) (a : α) (v : Fin n → α) :
    f ∘ Matrix.vecCons a v = Matrix.vecCons (f a) (f ∘ v) :=
  Fin.comp_cons f a v

theorem certificate_comp_vecEmpty {α β : Type*} (f : α → β) :
    f ∘ (Matrix.vecEmpty : Fin 0 → α) = (Matrix.vecEmpty : Fin 0 → β) := by
  funext i
  exact Fin.elim0 i

end ElevenSquare.Tasks.T06
