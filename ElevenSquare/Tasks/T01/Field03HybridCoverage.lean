import ElevenSquare.Tasks.T01.ClosedWindowCover

namespace ElevenSquare.Tasks.T01
noncomputable section

/-- 20 closed intervals covering the complete Field03 cell-4 chart. -/
def field03Cell04HybridWindows : List (ℚ × ℚ) := [
  (0, (1/256)),
  ((1/4096), (315/4096)),
  ((161/4096), (309/2048)),
  ((19/128), (5/32)),
  ((619/4096), (811/4096)),
  ((677/4096), (1195/4096)),
  ((131/512), (1293/4096)),
  ((5/16), (21/64)),
  ((647/2048), (897/2048)),
  ((7/16), (15/32)),
  ((1795/4096), (1119/2048)),
  ((65/128), (2531/4096)),
  ((19/32), (5/8)),
  ((633/1024), (2895/4096)),
  ((1433/2048), (743/1024)),
  ((23/32), (3/4)),
  ((2973/4096), (1697/2048)),
  ((1663/2048), (3863/4096)),
  ((1923/2048), (4069/4096)),
  ((63/64), 1)]

theorem field03_cell04_hybrid_coverage (M : ℝ → Prop)
    (h : ∀ w ∈ field03Cell04HybridWindows,
      ∀ t : ℝ, (w.1 : ℝ) ≤ t → t ≤ (w.2 : ℝ) → M t)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : M t := by
  apply closed_window_cover_sound field03Cell04HybridWindows ?_ M h t ht0 ht1
  norm_num [field03Cell04HybridWindows, ClosedWindowCoverCheck, ClosedWindowChain]

/-- 23 closed intervals covering the complete Field03 cell-8 chart. -/
def field03Cell08HybridWindows : List (ℚ × ℚ) := [
  (0, (1/64)),
  ((1/4096), (5/128)),
  ((75/4096), (189/2048)),
  ((343/4096), (309/2048)),
  ((1/8), (5/32)),
  ((619/4096), (837/4096)),
  ((203/1024), (679/2048)),
  ((5/16), (11/32)),
  ((1387/4096), (1605/4096)),
  ((717/2048), (897/2048)),
  ((7/16), (29/64)),
  ((1795/4096), (1001/2048)),
  ((247/512), (2531/4096)),
  ((2531/4096), (633/1024)),
  ((633/1024), (1423/2048)),
  ((355/512), (89/128)),
  ((2847/4096), (751/1024)),
  ((187/256), (47/64)),
  ((3005/4096), (3355/4096)),
  ((3301/4096), (1837/2048)),
  ((57/64), (115/128)),
  ((3675/4096), (127/128)),
  ((127/128), 1)]

theorem field03_cell08_hybrid_coverage (M : ℝ → Prop)
    (h : ∀ w ∈ field03Cell08HybridWindows,
      ∀ t : ℝ, (w.1 : ℝ) ≤ t → t ≤ (w.2 : ℝ) → M t)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : M t := by
  apply closed_window_cover_sound field03Cell08HybridWindows ?_ M h t ht0 ht1
  norm_num [field03Cell08HybridWindows, ClosedWindowCoverCheck, ClosedWindowChain]

end
end ElevenSquare.Tasks.T01

#print axioms ElevenSquare.Tasks.T01.field03_cell04_hybrid_coverage
#print axioms ElevenSquare.Tasks.T01.field03_cell08_hybrid_coverage
