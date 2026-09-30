import ElevenSquare.Cases
import ElevenSquare.Orientation
import ElevenSquare.Pending.Types
import Mathlib.Data.Finset.Sort

/-!
# Baseline root initialization

This module constructs a root from the actual closed Voronoi cells, with the
owners in increasing cell order.  It proves the required existential relabeling
for an arbitrary charted packing.  All hulls are initially empty; nonempty wall
seeds and certificate transitions still require their own geometric proofs.
No pending geometric theorem is used in these initialization lemmas.
-/

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

def baselineRationalSite (i : Fin 16) : ℚ × ℚ :=
  (![((104991 / 1000000), (265837 / 2000000)),
    ((186601 / 500000), (45503 / 1000000)),
    ((1267243 / 2000000), (34689 / 250000)),
    ((1731123 / 2000000), (25701 / 250000)),
    ((206181 / 2000000), (400379 / 1000000)),
    ((742311 / 2000000), (312933 / 1000000)),
    ((635257 / 1000000), (166409 / 400000)),
    ((445439 / 500000), (167763 / 500000)),
    ((54561 / 500000), (332237 / 500000)),
    ((364743 / 1000000), (233591 / 400000)),
    ((1257689 / 2000000), (687067 / 1000000)),
    ((1793819 / 2000000), (599621 / 1000000)),
    ((268877 / 2000000), (224299 / 250000)),
    ((732757 / 2000000), (215311 / 250000)),
    ((313399 / 500000), (954497 / 1000000)),
    ((895009 / 1000000), (1734163 / 2000000))] : Fin 16 → ℚ × ℚ) i

def baselineRationalCap : ℚ := 387708359002281417731 / 100000000000000000000

theorem baselineRationalCap_cast : (baselineRationalCap : ℝ) = coverCap := by
  norm_num [baselineRationalCap, coverCap]

theorem baselineRationalSite_cast (i : Fin 16) :
    realPoint (baselineRationalSite i) = coverSite i := by
  fin_cases i <;> norm_num [baselineRationalSite, realPoint, coverSite]

/-- The physical-center halfplane obtained from a normalized Voronoi bisector. -/
def baselineBisector (i j : Fin 16) : Halfplane :=
  let u := baselineRationalSite i
  let v := baselineRationalSite j
  ⟨2 * (v.1 - u.1), 2 * (v.2 - u.2),
    (baselineRationalCap - 1) * (v.1^2 + v.2^2 - (u.1^2 + u.2^2)) +
      (v.1 - u.1) + (v.2 - u.2)⟩

def baselineCenterBox : Polygon :=
  [⟨-1, 0, -1/2⟩, ⟨1, 0, baselineRationalCap - 1/2⟩,
   ⟨0, -1, -1/2⟩, ⟨0, 1, baselineRationalCap - 1/2⟩]

def baselineCellPolygon (i : Fin 16) : Polygon :=
  baselineCenterBox ++ (List.finRange 16).map (baselineBisector i)

theorem baselineBisector_contains {i j : Fin 16} {p : Point}
    (h : coordinateDistanceSq (normalizeCenter p) (coverSite i) ≤
      coordinateDistanceSq (normalizeCenter p) (coverSite j)) :
    (baselineBisector i j).contains p := by
  have hu : 0 < coverCap - 1 := sub_pos.mpr coverCap_gt_one
  have hid :
      (coverCap - 1) *
        (coordinateDistanceSq (normalizeCenter p) (coverSite j) -
          coordinateDistanceSq (normalizeCenter p) (coverSite i)) =
      (coverCap - 1) *
        ((coverSite j).1^2 + (coverSite j).2^2 -
          ((coverSite i).1^2 + (coverSite i).2^2)) +
      ((coverSite j).1 - (coverSite i).1) +
      ((coverSite j).2 - (coverSite i).2) -
      (2 * ((coverSite j).1 - (coverSite i).1) * p.1 +
        2 * ((coverSite j).2 - (coverSite i).2) * p.2) := by
    unfold coordinateDistanceSq normalizeCenter
    simp only [Prod.fst, Prod.snd]
    field_simp [ne_of_gt hu]
    ring
  have hn := mul_nonneg hu.le (sub_nonneg.mpr h)
  rw [hid] at hn
  have hsx (k : Fin 16) : ((baselineRationalSite k).1 : ℝ) = (coverSite k).1 :=
    congrArg Prod.fst (baselineRationalSite_cast k)
  have hsy (k : Fin 16) : ((baselineRationalSite k).2 : ℝ) = (coverSite k).2 :=
    congrArg Prod.snd (baselineRationalSite_cast k)
  dsimp only [baselineBisector, Halfplane.contains]
  push_cast
  rw [baselineRationalCap_cast, hsx i, hsx j, hsy i, hsy j]
  exact sub_nonneg.mp hn

theorem baselineCellPolygon_contains {i : Fin 16} {p : Point}
    (h : ClosedCell i (normalizeCenter p)) : p ∈ (baselineCellPolygon i).carrier := by
  have hu : 0 < coverCap - 1 := sub_pos.mpr coverCap_gt_one
  have hx0 := mul_nonneg h.1.1 hu.le
  have hx1 := mul_le_mul_of_nonneg_right h.1.2.1 hu.le
  have hy0 := mul_nonneg h.1.2.2.1 hu.le
  have hy1 := mul_le_mul_of_nonneg_right h.1.2.2.2 hu.le
  dsimp only [normalizeCenter] at hx0 hx1 hy0 hy1
  rw [div_mul_cancel₀ _ (ne_of_gt hu)] at hx0 hx1 hy0 hy1
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · simp only [baselineCenterBox, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    all_goals
      norm_num [Halfplane.contains, baselineRationalCap_cast]
      linarith
  · rcases List.mem_map.mp hl with ⟨j, _, rfl⟩
    exact baselineBisector_contains (h.2 j)

/-- A uniform, increasing owner order, independent of the particular packing.
The fallback is irrelevant whenever an eleven-square packing occupies the mask. -/
def baselineRoles (m : Finset (Fin 16)) : Owner → Fin 16 :=
  if h : m.card = 11 then m.orderEmbOfFin h else fun _ => 0

theorem baselineRoles_injective {m : Finset (Fin 16)} (hm : m.card = 11) :
    Function.Injective (baselineRoles m) := by
  simpa only [baselineRoles, dif_pos hm] using (m.orderEmbOfFin hm).injective

theorem baselineRoles_image {m : Finset (Fin 16)} (hm : m.card = 11) :
    Finset.univ.image (baselineRoles m) = m := by
  classical
  ext c
  simp only [baselineRoles, dif_pos hm, Finset.mem_image, Finset.mem_univ, true_and]
  change (∃ i, m.orderEmbOfFin hm i = c) ↔ c ∈ m
  have hr := m.range_orderEmbOfFin hm
  exact Set.ext_iff.mp hr c

theorem baseline_occupies_card {S : ℝ} {P : Packing 11 S}
    {m : Finset (Fin 16)} (h : Occupies P m) : m.card = 11 := by
  rcases h with ⟨a, ha, hm, _⟩
  rw [← hm, Finset.card_image_of_injective _ ha]
  simp

/-- Reindex the actual squares to match a fixed injective list of occupied cells. -/
theorem baseline_relabel_to_roles {S : ℝ} (P : Packing 11 S)
    (roles : Owner → Fin 16) (hinj : Function.Injective roles)
    (hocc : Occupies P (Finset.univ.image roles)) :
    ∃ perm : Equiv.Perm Owner, ∀ i,
      ClosedCell (roles i) (normalizeCenter ((relabelPacking P perm).squares i).center) := by
  classical
  rcases hocc with ⟨a, _, hmask, hcell⟩
  have hpre (i : Owner) : ∃ j : Owner, a j = roles i := by
    have hm : roles i ∈ Finset.univ.image a := by
      rw [hmask]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rcases Finset.mem_image.mp hm with ⟨j, _, hj⟩
    exact ⟨j, hj⟩
  choose g hg using hpre
  have hg_inj : Function.Injective g := by
    intro i j hij
    apply hinj
    rw [← hg i, ← hg j, hij]
  let perm : Equiv.Perm Owner :=
    Equiv.ofBijective g ⟨hg_inj, Finite.surjective_of_injective hg_inj⟩
  refine ⟨perm, ?_⟩
  intro i
  change ClosedCell (roles i) (normalizeCenter (P.squares (g i)).center)
  rw [← hg i]
  exact hcell (g i)

def baselineRoot (m : Finset (Fin 16)) : PoseState where
  rows := fun i => [⟨0, 1, baselineCellPolygon (baselineRoles m i)⟩]
  owned := fun _ => []

/-- The complete chart interval, including both endpoints, is retained. -/
theorem baseline_root_initialized {S : ℝ} (P : Packing 11 S)
    (m : Finset (Fin 16)) (hc : IsCharted P) (hocc : Occupies P m) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) (baselineRoot m) := by
  have hm := baseline_occupies_card hocc
  have himage := baselineRoles_image hm
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P (baselineRoles m)
    (baselineRoles_injective hm) (himage.symm ▸ hocc)
  refine ⟨perm, ?_, ?_⟩
  · intro i
    refine ⟨⟨0, 1, baselineCellPolygon (baselineRoles m i)⟩, by simp [baselineRoot], ?_⟩
    refine ⟨baselineCellPolygon_contains (hcell i), ?_⟩
    obtain ⟨t, ht0, ht1, haxis⟩ := hc (perm i)
    exact ⟨t, ht0, ht1, by simpa using ht0, by simpa using ht1, haxis⟩
  · intro i
    simp [baselineRoot, rationalHull]

end
end ElevenSquare.Tasks.T02
