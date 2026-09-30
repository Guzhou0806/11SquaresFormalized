import ElevenSquare.Tasks.T01.WallSeedRoot

namespace ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

/-- Exact rational half width of a unit square with chart parameter `t`. -/
def exactWallMarginQ (t : ℚ) : ℚ :=
  (1 - t ^ 2 + 2 * t) / (2 * (1 + t ^ 2))

theorem exactWallMarginQ_nonneg (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ exactWallMarginQ t := by
  have hp : 0 ≤ t * (1 - t) := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hn : 0 ≤ 1 - t ^ 2 + 2 * t := by nlinarith
  have hd : (0 : ℚ) < 2 * (1 + t ^ 2) := by positivity
  exact div_nonneg hn hd.le

theorem wall_endpoint_check (t h : ℚ) (hh : h ≤ exactWallMarginQ t) :
    0 ≤ 1 - 2 * h + 2 * t - (1 + 2 * h) * t ^ 2 := by
  have hd : (0 : ℚ) < 2 * (1 + t ^ 2) := by positivity
  have hc : h * (2 * (1 + t ^ 2)) ≤ 1 - t ^ 2 + 2 * t := by
    apply (le_div_iff hd).mp
    simpa [exactWallMarginQ] using hh
  calc
    0 ≤ (1 - t ^ 2 + 2 * t) - h * (2 * (1 + t ^ 2)) := sub_nonneg.mpr hc
    _ = 1 - 2 * h + 2 * t - (1 + 2 * h) * t ^ 2 := by ring

theorem min_wall_check (lo hi : ℚ)
    (hlo0 : 0 ≤ lo) (hlo1 : lo ≤ 1)
    (hhi0 : 0 ≤ hi) (hhi1 : hi ≤ 1) :
    BaselineWallCheck lo hi (min (exactWallMarginQ lo) (exactWallMarginQ hi)) := by
  unfold BaselineWallCheck
  refine ⟨le_min (exactWallMarginQ_nonneg lo hlo0 hlo1)
    (exactWallMarginQ_nonneg hi hhi0 hhi1), ?_, ?_⟩
  · exact wall_endpoint_check lo _ (min_le_left _ _)
  · exact wall_endpoint_check hi _ (min_le_right _ _)

def slabMargin (n : ℕ) (b : Fin n) : ℚ :=
  min (exactWallMarginQ ((b.val : ℚ) / n))
    (exactWallMarginQ (((b.val : ℚ) + 1) / n))

def slabRow (n : ℕ) (cell : Fin 16) (b : Fin n) : PoseRow :=
  uniformRow n (baselineSlab cell (slabMargin n b)) b

def slabRows (n : ℕ) (cell : Fin 16) : List PoseRow :=
  (List.finRange n).map (slabRow n cell)

theorem slabMargin_wall_check (n : ℕ) (hn : 0 < n) (b : Fin n) :
    BaselineWallCheck ((b.val : ℚ) / n) (((b.val : ℚ) + 1) / n)
      (slabMargin n b) := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hb : (b.val : ℚ) ≤ n := by exact_mod_cast (Nat.le_of_lt b.isLt)
  have hbs : (b.val : ℚ) + 1 ≤ n := by
    exact_mod_cast (Nat.succ_le_of_lt b.isLt)
  apply min_wall_check
  · exact div_nonneg (by positivity) hnq.le
  · exact (div_le_iff hnq).mpr (by simpa using hb)
  · exact div_nonneg (by positivity) hnq.le
  · exact (div_le_iff hnq).mpr (by simpa using hbs)

theorem slab_rows_contain (n : ℕ) (hn : 0 < n) (cell : Fin 16)
    (q : UnitSquare)
    (hcell : ClosedCell cell (normalizeCenter q.center))
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hchart : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) :
    RowsContain (slabRows n cell) q := by
  obtain ⟨t, ht0, ht1, ha⟩ := hchart
  obtain ⟨b, hbl, hbu⟩ := exists_uniform_bin n hn t ht0 ht1
  have hbl' : (((b.val : ℚ) / n : ℚ) : ℝ) ≤ t := by simpa using hbl
  have hbu' : t ≤ ((((b.val : ℚ) + 1) / n : ℚ) : ℝ) := by simpa using hbu
  have hs := baseline_slab_contains q cell ((b.val : ℚ) / n)
    (((b.val : ℚ) + 1) / n) (slabMargin n b) t
    (slabMargin_wall_check n hn b) hbl' hbu' ha hcont
    (baselineCellPolygon_contains hcell)
  refine ⟨slabRow n cell b, List.mem_map.mpr ⟨b, by simp, rfl⟩,
    ?_, t, ht0, ht1, ?_, ?_, ha⟩
  · exact hs
  · simpa [slabRow, uniformRow] using hbl
  · simpa [slabRow, uniformRow] using hbu

/-- Symbolic slab root for any occupied eleven-cell mask and owned-point
    selection. No archived wall polygon or facet implication is needed. -/
def symbolicSlabRoot (n : ℕ) (m : Finset (Fin 16))
    (owned : Fin 16 → List QPoint) : PoseState where
  rows := fun i => slabRows n (baselineRoles m i)
  owned := fun i => owned (baselineRoles m i)

theorem symbolic_slab_root_initialized (n : ℕ) (hn : 0 < n)
    (m : Finset (Fin 16)) (owned : Fin 16 → List QPoint)
    (hpoints : ∀ cell ∈ m, ∀ q : UnitSquare,
      ClosedCell cell (normalizeCenter q.center) →
      (∀ p, ClosedSquare q p → InContainer coverCap p) →
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q.axis = chartAxis t) →
      ∀ p ∈ owned cell, OpenSquare q (realPoint p))
    (P : Packing 11 coverCap) (hc : IsCharted P) (hocc : Occupies P m) :
    ∃ perm : Equiv.Perm Owner,
      StateHolds (relabelPacking P perm) (symbolicSlabRoot n m owned) := by
  have hm := baseline_occupies_card hocc
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P (baselineRoles m)
    (baselineRoles_injective hm) ((baselineRoles_image hm).symm ▸ hocc)
  have hmem (i : Owner) : baselineRoles m i ∈ m := by
    have hi : baselineRoles m i ∈ Finset.univ.image (baselineRoles m) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    exact Eq.mp (congrArg (fun cells => baselineRoles m i ∈ cells)
      (baselineRoles_image hm)) hi
  refine ⟨perm, ?_, ?_⟩
  · intro i
    exact slab_rows_contain n hn _ _ (hcell i)
      ((relabelPacking P perm).contained i) (hc (perm i))
  · intro i
    exact hull_owned_of_vertices _ _
      (hpoints _ (hmem i) _ (hcell i)
        ((relabelPacking P perm).contained i) (hc (perm i)))

end
end ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots

#print axioms ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots.symbolic_slab_root_initialized
