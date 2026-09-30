import ElevenSquare.Tasks.T07.CoordinateBridge
import ElevenSquare.Pending.S07_Bridge
import Mathlib.Tactic.FinCases

/-! The frozen D4 image relation preserves the original centered container.
This is the information needed after enlarging a hypothetical smaller packing. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def capHalfTurn (p : Point) : Point := (coverCap-p.1, coverCap-p.2)

def capView (g : Fin 4) (p : Point) : Point :=
  (![p, (coverCap-p.1,p.2), (coverCap-p.2,p.1), (p.2,p.1)] : Fin 4 → Point) g

theorem physicalSymmetry_eq (g : Fin 4) (flip : Bool) (p : Point) :
    physicalSymmetry g flip p =
      (if flip then capHalfTurn else id) (capView g p) := by
  have hu : coverCap-1 ≠ 0 := by norm_num [coverCap]
  cases flip <;> fin_cases g <;> apply Prod.ext <;>
    norm_num [physicalSymmetry, view, halfTurn, normalizeCenter, capView, capHalfTurn] <;>
    field_simp [hu] <;> ring

theorem capHalfTurn_involutive (p : Point) : capHalfTurn (capHalfTurn p) = p := by
  apply Prod.ext <;> dsimp [capHalfTurn] <;> ring

theorem capHalfTurn_centered (S : ℝ) (p : Point) :
    InCenteredContainer coverCap S (capHalfTurn p) ↔ InCenteredContainer coverCap S p := by
  have hn (x : ℝ) : coverCap-x-coverCap/2 = -(x-coverCap/2) := by ring
  simp only [InCenteredContainer, capHalfTurn, hn, abs_neg]

theorem capView_centered (g : Fin 4) (S : ℝ) (p : Point) :
    InCenteredContainer coverCap S (capView g p) ↔ InCenteredContainer coverCap S p := by
  have hn (x : ℝ) : coverCap-x-coverCap/2 = -(x-coverCap/2) := by ring
  fin_cases g <;> simp [capView, InCenteredContainer, hn, and_comm]
  all_goals simp only [abs_sub_comm (coverCap / 2) p.1,
    abs_sub_comm (coverCap / 2) p.2, and_comm] <;> simp

theorem physicalSymmetry_centered (g : Fin 4) (flip : Bool) (S : ℝ) (p : Point) :
    InCenteredContainer coverCap S (physicalSymmetry g flip p) ↔
      InCenteredContainer coverCap S p := by
  rw [physicalSymmetry_eq]
  cases flip
  · exact capView_centered g S p
  · exact (capHalfTurn_centered S _).trans (capView_centered g S p)

theorem capView_surjective (g : Fin 4) : Function.Surjective (capView g) := by
  intro p
  fin_cases g
  · exact ⟨p, rfl⟩
  · refine ⟨(coverCap-p.1,p.2), ?_⟩
    apply Prod.ext <;> simp [capView]
  · refine ⟨(p.2,coverCap-p.1), ?_⟩
    apply Prod.ext <;> simp [capView]
  · exact ⟨(p.2,p.1), rfl⟩

theorem physicalSymmetry_surjective (g : Fin 4) (flip : Bool) :
    Function.Surjective (physicalSymmetry g flip) := by
  intro p
  cases flip
  · obtain ⟨q, hq⟩ := capView_surjective g p
    exact ⟨q, by simpa only [physicalSymmetry_eq, Bool.false_eq_true, if_false, id_eq] using hq⟩
  · obtain ⟨q, hq⟩ := capView_surjective g (capHalfTurn p)
    refine ⟨q, ?_⟩
    rw [physicalSymmetry_eq]
    change capHalfTurn (capView g q) = p
    rw [hq, capHalfTurn_involutive]

theorem d4_preserves_centered {S : ℝ} {P Q : Packing 11 coverCap}
    (himage : D4Image P Q) (hsmall : CenteredPacking P S) : CenteredPacking Q S := by
  obtain ⟨g, flip, perm, hshape⟩ := himage
  intro i p hp
  obtain ⟨q, rfl⟩ := physicalSymmetry_surjective g flip p
  exact (physicalSymmetry_centered g flip S q).mpr
    (hsmall (perm i) q ((hshape i q).mp hp))

theorem T_lt_coverCap : T < coverCap := T_lt_U

/-- Uses the exact frozen upstream contracts. Their admissions, until integrated,
remain visible in the transitive axiom audit. -/
theorem case438_centered_reduction {S : ℝ} (P : Packing 11 S) (hST : S ≤ T) :
    ∃ Q : Packing 11 coverCap,
      Occupies Q (caseMask ⟨438, by omega⟩) ∧ CenteredPacking Q S := by
  have hSU : S ≤ coverCap := hST.trans T_lt_coverCap.le
  obtain ⟨Q, hD4, hocc⟩ := d4_forces_case438
    (fun k hk => all_noncandidates_excluded k hk) (P.enlargeCentered hSU)
  exact ⟨Q, hocc, d4_preserves_centered hD4 (enlargeCentered_preserves_side P hSU)⟩

end
end ElevenSquare.Tasks.T07
