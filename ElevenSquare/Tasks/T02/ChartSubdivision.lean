import ElevenSquare.Tasks.T02.Seeds
import Mathlib.Data.Real.Archimedean

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

/-- Closed uniform bins cover the entire chart, including the last endpoint. -/
theorem exists_uniform_bin (n : ℕ) (hn : 0 < n) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ i : Fin n, (i.val : ℝ) / n ≤ t ∧ t ≤ ((i.val : ℝ) + 1) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases ht : t = 1
  · subst t
    refine ⟨⟨n - 1, by omega⟩, ?_, ?_⟩
    · apply (div_le_iff hnR).mpr
      norm_num
    · apply (le_div_iff hnR).mpr
      have hs : n - 1 + 1 = n := by omega
      have hsR : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hs
      simpa using hsR.ge
  · have hlt : t < 1 := lt_of_le_of_ne ht1 ht
    have hnon : 0 ≤ (n : ℝ) * t := mul_nonneg hnR.le ht0
    have hfloor : Nat.floor ((n : ℝ) * t) < n :=
      (Nat.floor_lt hnon).mpr (by nlinarith)
    refine ⟨⟨Nat.floor ((n : ℝ) * t), hfloor⟩, ?_, ?_⟩
    · apply (div_le_iff hnR).mpr
      simpa [mul_comm] using Nat.floor_le hnon
    · apply (le_div_iff hnR).mpr
      simpa [mul_comm] using (Nat.lt_floor_add_one ((n : ℝ) * t)).le

def uniformRow (n : ℕ) (poly : Polygon) (i : Fin n) : PoseRow :=
  ⟨(i.val : ℚ) / n, ((i.val : ℚ) + 1) / n, poly⟩

def uniformRows (n : ℕ) (poly : Polygon) : List PoseRow :=
  (List.finRange n).map (uniformRow n poly)

theorem uniformRows_contains (n : ℕ) (hn : 0 < n) (poly : Polygon) (q : UnitSquare) :
    RowsContain (uniformRows n poly) q ↔
      q.center ∈ poly.carrier ∧
        ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t := by
  constructor
  · rintro ⟨r, hr, hp, t, ht0, ht1, _, _, ha⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    exact ⟨hp, t, ht0, ht1, ha⟩
  · rintro ⟨hp, t, ht0, ht1, ha⟩
    obtain ⟨i, hi0, hi1⟩ := exists_uniform_bin n hn t ht0 ht1
    refine ⟨uniformRow n poly i, List.mem_map.mpr ⟨i, by simp, rfl⟩,
      hp, t, ht0, ht1, ?_, ?_, ha⟩
    · simpa [uniformRow] using hi0
    · simpa [uniformRow] using hi1

/-- No wall-aware historical seed is silently substituted here: ownership is
exactly the previously proved conservative four-vertex seed. -/
def uniformSeedRoot (n : ℕ) (m : Finset (Fin 16)) : PoseState where
  rows := fun i => uniformRows n (baselineCellPolygon (baselineRoles m i))
  owned := (baselineSeedRoot m).owned

theorem uniform_seed_root_initialized {S : ℝ} (P : Packing 11 S)
    (n : ℕ) (hn : 0 < n) (m : Finset (Fin 16))
    (hc : IsCharted P) (hocc : Occupies P m) :
    ∃ perm : Equiv.Perm Owner,
      StateHolds (relabelPacking P perm) (uniformSeedRoot n m) := by
  have hm := baseline_occupies_card hocc
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P (baselineRoles m)
    (baselineRoles_injective hm) ((baselineRoles_image hm).symm ▸ hocc)
  refine ⟨perm, ?_, ?_⟩
  · intro i
    apply (uniformRows_contains n hn _ _).mpr
    exact ⟨baselineCellPolygon_contains (hcell i), hc (perm i)⟩
  · intro i
    exact hull_owned_of_vertices _ _ (baseline_seed_vertices_owned _ _ (hcell i))

end
end ElevenSquare.Tasks.T02
