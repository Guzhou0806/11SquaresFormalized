import ElevenSquare.Tasks.T06.BranchAliasDefinitions

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def aliasGap00_0 : Gap := Gap.wall 0 0 0

theorem aliasGap00_0_mem : aliasGap00_0 ∈ rowAliases 0 := List.mem_cons_self

theorem aliasGap00_0_enabled (r : Fin 512) : RawEnabled r aliasGap00_0 := True.intro

def aliasGap01_0 : Gap := Gap.wall 0 3 0

theorem aliasGap01_0_mem : aliasGap01_0 ∈ rowAliases 1 := List.mem_cons_self

theorem aliasGap01_0_enabled (r : Fin 512) : RawEnabled r aliasGap01_0 := True.intro

def aliasGap02_0 : Gap := Gap.wall 0 0 2

theorem aliasGap02_0_mem : aliasGap02_0 ∈ rowAliases 2 := List.mem_cons_self

theorem aliasGap02_0_enabled (r : Fin 512) : RawEnabled r aliasGap02_0 := True.intro

def aliasGap03_0 : Gap := Gap.wall 0 1 2

theorem aliasGap03_0_mem : aliasGap03_0 ∈ rowAliases 3 := List.mem_cons_self

theorem aliasGap03_0_enabled (r : Fin 512) : RawEnabled r aliasGap03_0 := True.intro

def aliasGap04_0 : Gap := Gap.wall 1 1 1

theorem aliasGap04_0_mem : aliasGap04_0 ∈ rowAliases 4 := List.mem_cons_self

theorem aliasGap04_0_enabled (r : Fin 512) : RawEnabled r aliasGap04_0 := True.intro

def aliasGap05_0 : Gap := Gap.wall 1 2 1

theorem aliasGap05_0_mem : aliasGap05_0 ∈ rowAliases 5 := List.mem_cons_self

theorem aliasGap05_0_enabled (r : Fin 512) : RawEnabled r aliasGap05_0 := True.intro

def aliasGap06_0 : Gap := Gap.wall 1 0 2

theorem aliasGap06_0_mem : aliasGap06_0 ∈ rowAliases 6 := List.mem_cons_self

theorem aliasGap06_0_enabled (r : Fin 512) : RawEnabled r aliasGap06_0 := True.intro

def aliasGap07_0 : Gap := Gap.wall 1 1 2

theorem aliasGap07_0_mem : aliasGap07_0 ∈ rowAliases 7 := List.mem_cons_self

theorem aliasGap07_0_enabled (r : Fin 512) : RawEnabled r aliasGap07_0 := True.intro

def aliasGap08_0 : Gap := Gap.wall 2 2 3

theorem aliasGap08_0_mem : aliasGap08_0 ∈ rowAliases 8 := List.mem_cons_self

theorem aliasGap08_0_enabled (r : Fin 512) : RawEnabled r aliasGap08_0 := True.intro

def aliasGap09_0 : Gap := Gap.wall 2 3 3

theorem aliasGap09_0_mem : aliasGap09_0 ∈ rowAliases 9 := List.mem_cons_self

theorem aliasGap09_0_enabled (r : Fin 512) : RawEnabled r aliasGap09_0 := True.intro

def aliasGap10_0 : Gap := Gap.wall 3 0 0

theorem aliasGap10_0_mem : aliasGap10_0 ∈ rowAliases 10 := List.mem_cons_self

theorem aliasGap10_0_enabled (r : Fin 512) : RawEnabled r aliasGap10_0 := True.intro

def aliasGap11_0 : Gap := Gap.wall 3 3 0

theorem aliasGap11_0_mem : aliasGap11_0 ∈ rowAliases 11 := List.mem_cons_self

theorem aliasGap11_0_enabled (r : Fin 512) : RawEnabled r aliasGap11_0 := True.intro

def aliasGap12_0 : Gap := Gap.wall 3 2 3

theorem aliasGap12_0_mem : aliasGap12_0 ∈ rowAliases 12 := List.mem_cons_self

theorem aliasGap12_0_enabled (r : Fin 512) : RawEnabled r aliasGap12_0 := True.intro

def aliasGap13_0 : Gap := Gap.wall 3 3 3

theorem aliasGap13_0_mem : aliasGap13_0 ∈ rowAliases 13 := List.mem_cons_self

theorem aliasGap13_0_enabled (r : Fin 512) : RawEnabled r aliasGap13_0 := True.intro

def aliasGap14_0 : Gap := Gap.wall 4 2 3

theorem aliasGap14_0_mem : aliasGap14_0 ∈ rowAliases 14 := List.mem_cons_self

theorem aliasGap14_0_enabled (r : Fin 512) : RawEnabled r aliasGap14_0 := True.intro

def aliasGap15_0 : Gap := Gap.wall 4 3 3

theorem aliasGap15_0_mem : aliasGap15_0 ∈ rowAliases 15 := List.mem_cons_self

theorem aliasGap15_0_enabled (r : Fin 512) : RawEnabled r aliasGap15_0 := True.intro

def aliasGap16_0 : Gap := Gap.wall 5 0 0

theorem aliasGap16_0_mem : aliasGap16_0 ∈ rowAliases 16 := List.mem_cons_self

theorem aliasGap16_0_enabled (r : Fin 512) : RawEnabled r aliasGap16_0 := True.intro

def aliasGap17_0 : Gap := Gap.wall 5 3 0

theorem aliasGap17_0_mem : aliasGap17_0 ∈ rowAliases 17 := List.mem_cons_self

theorem aliasGap17_0_enabled (r : Fin 512) : RawEnabled r aliasGap17_0 := True.intro

def aliasGap18_0 : Gap := Gap.wall 7 0 2

theorem aliasGap18_0_mem : aliasGap18_0 ∈ rowAliases 18 := List.mem_cons_self

theorem aliasGap18_0_enabled (r : Fin 512) : RawEnabled r aliasGap18_0 := True.intro

def aliasGap19_0 : Gap := Gap.wall 10 1 1

theorem aliasGap19_0_mem : aliasGap19_0 ∈ rowAliases 19 := List.mem_cons_self

theorem aliasGap19_0_enabled (r : Fin 512) : RawEnabled r aliasGap19_0 := True.intro

def aliasGap20_0 : Gap := Gap.pair ({owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true}) 2

theorem aliasGap20_0_mem : aliasGap20_0 ∈ rowAliases 20 := List.mem_cons_self

theorem aliasGap20_0_enabled (r : Fin 512) (hid : rawSelections r 0 = 7) :
    RawEnabled r aliasGap20_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 6, other := 0, distinct := by decide, perpendicular := false, reverse := true} : SeparationFeature)
  refine ⟨0, ?_⟩
  rw [hid]
  rfl

def aliasGap21_0 : Gap := Gap.pair ({owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true}) 3

theorem aliasGap21_0_mem : aliasGap21_0 ∈ rowAliases 21 := List.mem_cons_self

theorem aliasGap21_0_enabled (r : Fin 512) (hid : rawSelections r 1 = 12) :
    RawEnabled r aliasGap21_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 9, other := 1, distinct := by decide, perpendicular := true, reverse := true} : SeparationFeature)
  refine ⟨1, ?_⟩
  rw [hid]
  rfl

def aliasGap22_0 : Gap := Gap.pair ({owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false}) 0

theorem aliasGap22_0_mem : aliasGap22_0 ∈ rowAliases 22 := List.mem_cons_self

theorem aliasGap22_0_enabled (r : Fin 512) (hid : rawSelections r 2 = 22) :
    RawEnabled r aliasGap22_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 8, other := 2, distinct := by decide, perpendicular := false, reverse := false} : SeparationFeature)
  refine ⟨2, ?_⟩
  rw [hid]
  rfl

def aliasGap23_0 : Gap := Gap.pair ({owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false}) 1

theorem aliasGap23_0_mem : aliasGap23_0 ∈ rowAliases 23 := List.mem_cons_self

theorem aliasGap23_0_enabled (r : Fin 512) (hid : rawSelections r 3 = 29) :
    RawEnabled r aliasGap23_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 10, other := 2, distinct := by decide, perpendicular := true, reverse := false} : SeparationFeature)
  refine ⟨3, ?_⟩
  rw [hid]
  rfl

def aliasGap24_0 : Gap := Gap.pair ({owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false}) 0

theorem aliasGap24_0_mem : aliasGap24_0 ∈ rowAliases 24 := List.mem_cons_self

theorem aliasGap24_0_enabled (r : Fin 512) (hid : rawSelections r 4 = 35) :
    RawEnabled r aliasGap24_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false} : SeparationFeature)
  refine ⟨4, ?_⟩
  rw [hid]
  rfl

def aliasGap24_1 : Gap := Gap.pair ({owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true}) 1

theorem aliasGap24_1_mem : aliasGap24_1 ∈ rowAliases 24 := List.mem_cons_of_mem _ (List.mem_cons_self)

theorem aliasGap24_1_enabled (r : Fin 512) (hid : rawSelections r 4 = 39) :
    RawEnabled r aliasGap24_1 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true} : SeparationFeature)
  refine ⟨4, ?_⟩
  rw [hid]
  rfl

def aliasGap25_0 : Gap := Gap.pair ({owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false}) 3

theorem aliasGap25_0_mem : aliasGap25_0 ∈ rowAliases 25 := List.mem_cons_self

theorem aliasGap25_0_enabled (r : Fin 512) (hid : rawSelections r 4 = 35) :
    RawEnabled r aliasGap25_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 3, other := 4, distinct := by decide, perpendicular := false, reverse := false} : SeparationFeature)
  refine ⟨4, ?_⟩
  rw [hid]
  rfl

def aliasGap25_1 : Gap := Gap.pair ({owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true}) 2

theorem aliasGap25_1_mem : aliasGap25_1 ∈ rowAliases 25 := List.mem_cons_of_mem _ (List.mem_cons_self)

theorem aliasGap25_1_enabled (r : Fin 512) (hid : rawSelections r 4 = 39) :
    RawEnabled r aliasGap25_1 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 4, other := 3, distinct := by decide, perpendicular := false, reverse := true} : SeparationFeature)
  refine ⟨4, ?_⟩
  rw [hid]
  rfl

def aliasGap26_0 : Gap := Gap.pair ({owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true}) 2

theorem aliasGap26_0_mem : aliasGap26_0 ∈ rowAliases 26 := List.mem_cons_self

theorem aliasGap26_0_enabled (r : Fin 512) (hid : rawSelections r 5 = 41) :
    RawEnabled r aliasGap26_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true} : SeparationFeature)
  refine ⟨5, ?_⟩
  rw [hid]
  rfl

def aliasGap26_1 : Gap := Gap.pair ({owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false}) 1

theorem aliasGap26_1_mem : aliasGap26_1 ∈ rowAliases 26 := List.mem_cons_of_mem _ (List.mem_cons_self)

theorem aliasGap26_1_enabled (r : Fin 512) (hid : rawSelections r 5 = 45) :
    RawEnabled r aliasGap26_1 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false} : SeparationFeature)
  refine ⟨5, ?_⟩
  rw [hid]
  rfl

def aliasGap27_0 : Gap := Gap.pair ({owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true}) 3

theorem aliasGap27_0_mem : aliasGap27_0 ∈ rowAliases 27 := List.mem_cons_self

theorem aliasGap27_0_enabled (r : Fin 512) (hid : rawSelections r 5 = 41) :
    RawEnabled r aliasGap27_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 3, other := 5, distinct := by decide, perpendicular := true, reverse := true} : SeparationFeature)
  refine ⟨5, ?_⟩
  rw [hid]
  rfl

def aliasGap27_1 : Gap := Gap.pair ({owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false}) 0

theorem aliasGap27_1_mem : aliasGap27_1 ∈ rowAliases 27 := List.mem_cons_of_mem _ (List.mem_cons_self)

theorem aliasGap27_1_enabled (r : Fin 512) (hid : rawSelections r 5 = 45) :
    RawEnabled r aliasGap27_1 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 5, other := 3, distinct := by decide, perpendicular := true, reverse := false} : SeparationFeature)
  refine ⟨5, ?_⟩
  rw [hid]
  rfl

def aliasGap28_0 : Gap := Gap.pair ({owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true}) 2

theorem aliasGap28_0_mem : aliasGap28_0 ∈ rowAliases 28 := List.mem_cons_self

theorem aliasGap28_0_enabled (r : Fin 512) (hid : rawSelections r 6 = 49) :
    RawEnabled r aliasGap28_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true} : SeparationFeature)
  refine ⟨6, ?_⟩
  rw [hid]
  rfl

def aliasGap28_1 : Gap := Gap.pair ({owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false}) 0

theorem aliasGap28_1_mem : aliasGap28_1 ∈ rowAliases 28 := List.mem_cons_of_mem _ (List.mem_cons_self)

theorem aliasGap28_1_enabled (r : Fin 512) (hid : rawSelections r 6 = 53) :
    RawEnabled r aliasGap28_1 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false} : SeparationFeature)
  refine ⟨6, ?_⟩
  rw [hid]
  rfl

def aliasGap29_0 : Gap := Gap.pair ({owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true}) 3

theorem aliasGap29_0_mem : aliasGap29_0 ∈ rowAliases 29 := List.mem_cons_self

theorem aliasGap29_0_enabled (r : Fin 512) (hid : rawSelections r 6 = 49) :
    RawEnabled r aliasGap29_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 4, other := 5, distinct := by decide, perpendicular := true, reverse := true} : SeparationFeature)
  refine ⟨6, ?_⟩
  rw [hid]
  rfl

def aliasGap30_0 : Gap := Gap.pair ({owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false}) 1

theorem aliasGap30_0_mem : aliasGap30_0 ∈ rowAliases 30 := List.mem_cons_self

theorem aliasGap30_0_enabled (r : Fin 512) (hid : rawSelections r 7 = 61) :
    RawEnabled r aliasGap30_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 8, other := 4, distinct := by decide, perpendicular := true, reverse := false} : SeparationFeature)
  refine ⟨7, ?_⟩
  rw [hid]
  rfl

def aliasGap31_0 : Gap := Gap.pair ({owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false}) 1

theorem aliasGap31_0_mem : aliasGap31_0 ∈ rowAliases 31 := List.mem_cons_self

theorem aliasGap31_0_enabled (r : Fin 512) (hid : rawSelections r 8 = 69) :
    RawEnabled r aliasGap31_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 6, other := 5, distinct := by decide, perpendicular := true, reverse := false} : SeparationFeature)
  refine ⟨8, ?_⟩
  rw [hid]
  rfl

def aliasGap32_0 : Gap := Gap.pair ({owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true}) 2

theorem aliasGap32_0_mem : aliasGap32_0 ∈ rowAliases 32 := List.mem_cons_self

theorem aliasGap32_0_enabled (r : Fin 512) (hid : rawSelections r 9 = 73) :
    RawEnabled r aliasGap32_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true} : SeparationFeature)
  refine ⟨9, ?_⟩
  rw [hid]
  rfl

def aliasGap33_0 : Gap := Gap.pair ({owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true}) 3

theorem aliasGap33_0_mem : aliasGap33_0 ∈ rowAliases 33 := List.mem_cons_self

theorem aliasGap33_0_enabled (r : Fin 512) (hid : rawSelections r 9 = 73) :
    RawEnabled r aliasGap33_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 6, other := 7, distinct := by decide, perpendicular := true, reverse := true} : SeparationFeature)
  refine ⟨9, ?_⟩
  rw [hid]
  rfl

def aliasGap34_0 : Gap := Gap.pair ({owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true}) 1

theorem aliasGap34_0_mem : aliasGap34_0 ∈ rowAliases 34 := List.mem_cons_self

theorem aliasGap34_0_enabled (r : Fin 512) (hid : rawSelections r 10 = 87) :
    RawEnabled r aliasGap34_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true} : SeparationFeature)
  refine ⟨10, ?_⟩
  rw [hid]
  rfl

def aliasGap35_0 : Gap := Gap.pair ({owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true}) 2

theorem aliasGap35_0_mem : aliasGap35_0 ∈ rowAliases 35 := List.mem_cons_self

theorem aliasGap35_0_enabled (r : Fin 512) (hid : rawSelections r 10 = 87) :
    RawEnabled r aliasGap35_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 8, other := 6, distinct := by decide, perpendicular := false, reverse := true} : SeparationFeature)
  refine ⟨10, ?_⟩
  rw [hid]
  rfl

def aliasGap36_0 : Gap := Gap.pair ({owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true}) 1

theorem aliasGap36_0_mem : aliasGap36_0 ∈ rowAliases 36 := List.mem_cons_self

theorem aliasGap36_0_enabled (r : Fin 512) (hid : rawSelections r 11 = 95) :
    RawEnabled r aliasGap36_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true} : SeparationFeature)
  refine ⟨11, ?_⟩
  rw [hid]
  rfl

def aliasGap37_0 : Gap := Gap.pair ({owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true}) 2

theorem aliasGap37_0_mem : aliasGap37_0 ∈ rowAliases 37 := List.mem_cons_self

theorem aliasGap37_0_enabled (r : Fin 512) (hid : rawSelections r 11 = 95) :
    RawEnabled r aliasGap37_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 9, other := 7, distinct := by decide, perpendicular := false, reverse := true} : SeparationFeature)
  refine ⟨11, ?_⟩
  rw [hid]
  rfl

def aliasGap38_0 : Gap := Gap.pair ({owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true}) 2

theorem aliasGap38_0_mem : aliasGap38_0 ∈ rowAliases 38 := List.mem_cons_self

theorem aliasGap38_0_enabled (r : Fin 512) (hid : rawSelections r 12 = 97) :
    RawEnabled r aliasGap38_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true} : SeparationFeature)
  refine ⟨12, ?_⟩
  rw [hid]
  rfl

def aliasGap39_0 : Gap := Gap.pair ({owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true}) 3

theorem aliasGap39_0_mem : aliasGap39_0 ∈ rowAliases 39 := List.mem_cons_self

theorem aliasGap39_0_enabled (r : Fin 512) (hid : rawSelections r 12 = 97) :
    RawEnabled r aliasGap39_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 8, other := 9, distinct := by decide, perpendicular := true, reverse := true} : SeparationFeature)
  refine ⟨12, ?_⟩
  rw [hid]
  rfl

def aliasGap40_0 : Gap := Gap.pair ({owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false}) 0

theorem aliasGap40_0_mem : aliasGap40_0 ∈ rowAliases 40 := List.mem_cons_self

theorem aliasGap40_0_enabled (r : Fin 512) (hid : rawSelections r 13 = 107) :
    RawEnabled r aliasGap40_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false} : SeparationFeature)
  refine ⟨13, ?_⟩
  rw [hid]
  rfl

def aliasGap41_0 : Gap := Gap.pair ({owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false}) 3

theorem aliasGap41_0_mem : aliasGap41_0 ∈ rowAliases 41 := List.mem_cons_self

theorem aliasGap41_0_enabled (r : Fin 512) (hid : rawSelections r 13 = 107) :
    RawEnabled r aliasGap41_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 9, other := 10, distinct := by decide, perpendicular := false, reverse := false} : SeparationFeature)
  refine ⟨13, ?_⟩
  rw [hid]
  rfl

def aliasGap42_0 : Gap := Gap.pair ({owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false}) 1

theorem aliasGap42_0_mem : aliasGap42_0 ∈ rowAliases 42 := List.mem_cons_self

theorem aliasGap42_0_enabled (r : Fin 512) (hid : rawSelections r 6 = 53) :
    RawEnabled r aliasGap42_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 5, other := 4, distinct := by decide, perpendicular := true, reverse := false} : SeparationFeature)
  refine ⟨6, ?_⟩
  rw [hid]
  rfl

def aliasGap43_0 : Gap := Gap.pair ({owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true}) 2

theorem aliasGap43_0_mem : aliasGap43_0 ∈ rowAliases 43 := List.mem_cons_self

theorem aliasGap43_0_enabled (r : Fin 512) (hid : rawSelections r 6 = 50) :
    RawEnabled r aliasGap43_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true} : SeparationFeature)
  refine ⟨6, ?_⟩
  rw [hid]
  rfl

def aliasGap43_1 : Gap := Gap.pair ({owner := 5, other := 4, distinct := by decide, perpendicular := false, reverse := false}) 0

theorem aliasGap43_1_mem : aliasGap43_1 ∈ rowAliases 43 := List.mem_cons_of_mem _ (List.mem_cons_self)

theorem aliasGap43_1_enabled (r : Fin 512) (hid : rawSelections r 6 = 54) :
    RawEnabled r aliasGap43_1 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 5, other := 4, distinct := by decide, perpendicular := false, reverse := false} : SeparationFeature)
  refine ⟨6, ?_⟩
  rw [hid]
  rfl

def aliasGap44_0 : Gap := Gap.pair ({owner := 5, other := 4, distinct := by decide, perpendicular := false, reverse := false}) 3

theorem aliasGap44_0_mem : aliasGap44_0 ∈ rowAliases 44 := List.mem_cons_self

theorem aliasGap44_0_enabled (r : Fin 512) (hid : rawSelections r 6 = 54) :
    RawEnabled r aliasGap44_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 5, other := 4, distinct := by decide, perpendicular := false, reverse := false} : SeparationFeature)
  refine ⟨6, ?_⟩
  rw [hid]
  rfl

def aliasGap45_0 : Gap := Gap.pair ({owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true}) 1

theorem aliasGap45_0_mem : aliasGap45_0 ∈ rowAliases 45 := List.mem_cons_self

theorem aliasGap45_0_enabled (r : Fin 512) (hid : rawSelections r 6 = 50) :
    RawEnabled r aliasGap45_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 4, other := 5, distinct := by decide, perpendicular := false, reverse := true} : SeparationFeature)
  refine ⟨6, ?_⟩
  rw [hid]
  rfl

def aliasGap46_0 : Gap := Gap.pair ({owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true}) 1

theorem aliasGap46_0_mem : aliasGap46_0 ∈ rowAliases 46 := List.mem_cons_self

theorem aliasGap46_0_enabled (r : Fin 512) (hid : rawSelections r 13 = 111) :
    RawEnabled r aliasGap46_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true} : SeparationFeature)
  refine ⟨13, ?_⟩
  rw [hid]
  rfl

def aliasGap47_0 : Gap := Gap.pair ({owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true}) 2

theorem aliasGap47_0_mem : aliasGap47_0 ∈ rowAliases 47 := List.mem_cons_self

theorem aliasGap47_0_enabled (r : Fin 512) (hid : rawSelections r 13 = 111) :
    RawEnabled r aliasGap47_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 10, other := 9, distinct := by decide, perpendicular := false, reverse := true} : SeparationFeature)
  refine ⟨13, ?_⟩
  rw [hid]
  rfl

def aliasGap48_0 : Gap := Gap.pair ({owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false}) 0

theorem aliasGap48_0_mem : aliasGap48_0 ∈ rowAliases 48 := List.mem_cons_self

theorem aliasGap48_0_enabled (r : Fin 512) (hid : rawSelections r 12 = 101) :
    RawEnabled r aliasGap48_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false} : SeparationFeature)
  refine ⟨12, ?_⟩
  rw [hid]
  rfl

def aliasGap49_0 : Gap := Gap.pair ({owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false}) 1

theorem aliasGap49_0_mem : aliasGap49_0 ∈ rowAliases 49 := List.mem_cons_self

theorem aliasGap49_0_enabled (r : Fin 512) (hid : rawSelections r 12 = 101) :
    RawEnabled r aliasGap49_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 9, other := 8, distinct := by decide, perpendicular := true, reverse := false} : SeparationFeature)
  refine ⟨12, ?_⟩
  rw [hid]
  rfl

def aliasGap50_0 : Gap := Gap.pair ({owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := false}) 0

theorem aliasGap50_0_mem : aliasGap50_0 ∈ rowAliases 50 := List.mem_cons_self

theorem aliasGap50_0_enabled (r : Fin 512) (hid : rawSelections r 11 = 91) :
    RawEnabled r aliasGap50_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := false} : SeparationFeature)
  refine ⟨11, ?_⟩
  rw [hid]
  rfl

def aliasGap51_0 : Gap := Gap.pair ({owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := false}) 3

theorem aliasGap51_0_mem : aliasGap51_0 ∈ rowAliases 51 := List.mem_cons_self

theorem aliasGap51_0_enabled (r : Fin 512) (hid : rawSelections r 11 = 91) :
    RawEnabled r aliasGap51_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 7, other := 9, distinct := by decide, perpendicular := false, reverse := false} : SeparationFeature)
  refine ⟨11, ?_⟩
  rw [hid]
  rfl

def aliasGap52_0 : Gap := Gap.pair ({owner := 7, other := 6, distinct := by decide, perpendicular := true, reverse := false}) 0

theorem aliasGap52_0_mem : aliasGap52_0 ∈ rowAliases 52 := List.mem_cons_self

theorem aliasGap52_0_enabled (r : Fin 512) (hid : rawSelections r 9 = 77) :
    RawEnabled r aliasGap52_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 7, other := 6, distinct := by decide, perpendicular := true, reverse := false} : SeparationFeature)
  refine ⟨9, ?_⟩
  rw [hid]
  rfl

def aliasGap53_0 : Gap := Gap.pair ({owner := 7, other := 6, distinct := by decide, perpendicular := true, reverse := false}) 1

theorem aliasGap53_0_mem : aliasGap53_0 ∈ rowAliases 53 := List.mem_cons_self

theorem aliasGap53_0_enabled (r : Fin 512) (hid : rawSelections r 9 = 77) :
    RawEnabled r aliasGap53_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 7, other := 6, distinct := by decide, perpendicular := true, reverse := false} : SeparationFeature)
  refine ⟨9, ?_⟩
  rw [hid]
  rfl

def aliasGap54_0 : Gap := Gap.pair ({owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false}) 0

theorem aliasGap54_0_mem : aliasGap54_0 ∈ rowAliases 54 := List.mem_cons_self

theorem aliasGap54_0_enabled (r : Fin 512) (hid : rawSelections r 10 = 83) :
    RawEnabled r aliasGap54_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false} : SeparationFeature)
  refine ⟨10, ?_⟩
  rw [hid]
  rfl

def aliasGap55_0 : Gap := Gap.pair ({owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false}) 3

theorem aliasGap55_0_mem : aliasGap55_0 ∈ rowAliases 55 := List.mem_cons_self

theorem aliasGap55_0_enabled (r : Fin 512) (hid : rawSelections r 10 = 83) :
    RawEnabled r aliasGap55_0 := by
  change ∃ pair, allFeatures (rawSelections r pair) = ({owner := 6, other := 8, distinct := by decide, perpendicular := false, reverse := false} : SeparationFeature)
  refine ⟨10, ?_⟩
  rw [hid]
  rfl


end
end ElevenSquare.Tasks.T06
