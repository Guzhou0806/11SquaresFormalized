import ElevenSquare.Tasks.T06.BranchAliasFacts

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem raw_alias_cover_048 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 48) row), RawEnabled 48 g := by
  have hsel : rawSelections 48 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 83, 91, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 48 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 48⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 48⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 48⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 48⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 48⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 48⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 48⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 48⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 48⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 48⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 48⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 48⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 48⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 48⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 48⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 48⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 48⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 48⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 48⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 48⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 48 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 48 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 48 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 48 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 48 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 48 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 48 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 48 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 48 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 48 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 48 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 48 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 48 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 48 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 48 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 48 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 48 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 48 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 48 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 48 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 48 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 48 (congrFun hsel 13)⟩

theorem raw_alias_cover_049 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 49) row), RawEnabled 49 g := by
  have hsel : rawSelections 49 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 83, 91, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 49 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 49⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 49⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 49⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 49⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 49⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 49⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 49⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 49⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 49⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 49⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 49⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 49⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 49⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 49⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 49⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 49⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 49⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 49⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 49⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 49⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 49 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 49 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 49 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 49 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 49 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 49 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 49 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 49 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 49 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 49 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 49 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 49 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 49 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 49 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 49 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 49 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 49 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 49 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 49 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 49 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 49 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 49 (congrFun hsel 13)⟩

theorem raw_alias_cover_050 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 50) row), RawEnabled 50 g := by
  have hsel : rawSelections 50 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 83, 91, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 50 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 50⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 50⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 50⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 50⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 50⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 50⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 50⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 50⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 50⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 50⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 50⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 50⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 50⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 50⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 50⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 50⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 50⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 50⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 50⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 50⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 50 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 50 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 50 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 50 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 50 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 50 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 50 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 50 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 50 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 50 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 50 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 50 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 50 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 50 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 50 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 50 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 50 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 50 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 50 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 50 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 50 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 50 (congrFun hsel 13)⟩

theorem raw_alias_cover_051 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 51) row), RawEnabled 51 g := by
  have hsel : rawSelections 51 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 83, 91, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 51 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 51⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 51⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 51⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 51⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 51⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 51⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 51⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 51⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 51⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 51⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 51⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 51⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 51⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 51⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 51⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 51⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 51⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 51⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 51⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 51⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 51 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 51 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 51 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 51 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 51 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 51 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 51 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 51 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 51 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 51 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 51 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 51 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 51 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 51 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 51 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 51 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 51 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 51 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 51 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 51 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 51 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 51 (congrFun hsel 13)⟩

theorem raw_alias_cover_052 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 52) row), RawEnabled 52 g := by
  have hsel : rawSelections 52 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 83, 95, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 52 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 52⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 52⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 52⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 52⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 52⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 52⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 52⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 52⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 52⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 52⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 52⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 52⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 52⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 52⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 52⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 52⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 52⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 52⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 52⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 52⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 52 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 52 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 52 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 52 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 52 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 52 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 52 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 52 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 52 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 52 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 52 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 52 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 52 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 52 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 52 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 52 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 52 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 52 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 52 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 52 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 52 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 52 (congrFun hsel 13)⟩

theorem raw_alias_cover_053 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 53) row), RawEnabled 53 g := by
  have hsel : rawSelections 53 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 83, 95, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 53 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 53⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 53⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 53⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 53⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 53⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 53⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 53⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 53⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 53⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 53⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 53⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 53⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 53⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 53⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 53⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 53⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 53⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 53⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 53⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 53⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 53 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 53 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 53 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 53 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 53 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 53 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 53 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 53 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 53 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 53 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 53 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 53 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 53 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 53 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 53 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 53 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 53 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 53 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 53 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 53 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 53 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 53 (congrFun hsel 13)⟩

theorem raw_alias_cover_054 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 54) row), RawEnabled 54 g := by
  have hsel : rawSelections 54 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 83, 95, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 54 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 54⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 54⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 54⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 54⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 54⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 54⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 54⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 54⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 54⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 54⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 54⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 54⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 54⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 54⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 54⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 54⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 54⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 54⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 54⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 54⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 54 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 54 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 54 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 54 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 54 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 54 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 54 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 54 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 54 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 54 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 54 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 54 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 54 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 54 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 54 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 54 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 54 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 54 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 54 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 54 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 54 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 54 (congrFun hsel 13)⟩

theorem raw_alias_cover_055 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 55) row), RawEnabled 55 g := by
  have hsel : rawSelections 55 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 83, 95, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 55 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 55⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 55⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 55⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 55⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 55⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 55⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 55⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 55⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 55⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 55⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 55⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 55⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 55⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 55⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 55⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 55⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 55⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 55⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 55⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 55⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 55 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 55 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 55 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 55 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 55 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 55 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 55 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 55 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 55 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 55 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 55 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 55 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 55 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 55 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 55 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 55 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 55 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 55 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 55 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 55 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 55 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 55 (congrFun hsel 13)⟩

theorem raw_alias_cover_056 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 56) row), RawEnabled 56 g := by
  have hsel : rawSelections 56 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 87, 91, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 56 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 56⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 56⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 56⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 56⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 56⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 56⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 56⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 56⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 56⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 56⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 56⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 56⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 56⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 56⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 56⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 56⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 56⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 56⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 56⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 56⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 56 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 56 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 56 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 56 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 56 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 56 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 56 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 56 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 56 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 56 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 56 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 56 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 56 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 56 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 56 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 56 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 56 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 56 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 56 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 56 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 56 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 56 (congrFun hsel 13)⟩

theorem raw_alias_cover_057 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 57) row), RawEnabled 57 g := by
  have hsel : rawSelections 57 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 87, 91, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 57 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 57⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 57⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 57⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 57⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 57⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 57⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 57⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 57⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 57⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 57⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 57⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 57⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 57⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 57⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 57⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 57⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 57⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 57⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 57⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 57⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 57 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 57 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 57 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 57 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 57 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 57 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 57 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 57 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 57 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 57 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 57 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 57 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 57 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 57 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 57 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 57 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 57 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 57 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 57 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 57 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 57 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 57 (congrFun hsel 13)⟩

theorem raw_alias_cover_058 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 58) row), RawEnabled 58 g := by
  have hsel : rawSelections 58 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 87, 91, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 58 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 58⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 58⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 58⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 58⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 58⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 58⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 58⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 58⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 58⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 58⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 58⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 58⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 58⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 58⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 58⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 58⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 58⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 58⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 58⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 58⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 58 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 58 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 58 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 58 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 58 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 58 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 58 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 58 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 58 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 58 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 58 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 58 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 58 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 58 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 58 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 58 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 58 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 58 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 58 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 58 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 58 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 58 (congrFun hsel 13)⟩

theorem raw_alias_cover_059 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 59) row), RawEnabled 59 g := by
  have hsel : rawSelections 59 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 87, 91, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 59 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 59⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 59⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 59⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 59⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 59⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 59⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 59⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 59⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 59⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 59⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 59⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 59⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 59⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 59⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 59⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 59⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 59⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 59⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 59⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 59⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 59 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 59 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 59 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 59 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 59 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 59 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 59 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 59 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 59 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 59 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 59 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 59 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 59 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 59 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 59 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 59 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 59 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 59 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 59 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 59 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 59 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 59 (congrFun hsel 13)⟩

theorem raw_alias_cover_060 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 60) row), RawEnabled 60 g := by
  have hsel : rawSelections 60 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 87, 95, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 60 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 60⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 60⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 60⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 60⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 60⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 60⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 60⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 60⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 60⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 60⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 60⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 60⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 60⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 60⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 60⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 60⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 60⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 60⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 60⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 60⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 60 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 60 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 60 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 60 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 60 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 60 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 60 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 60 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 60 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 60 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 60 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 60 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 60 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 60 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 60 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 60 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 60 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 60 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 60 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 60 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 60 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 60 (congrFun hsel 13)⟩

theorem raw_alias_cover_061 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 61) row), RawEnabled 61 g := by
  have hsel : rawSelections 61 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 87, 95, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 61 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 61⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 61⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 61⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 61⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 61⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 61⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 61⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 61⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 61⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 61⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 61⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 61⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 61⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 61⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 61⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 61⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 61⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 61⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 61⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 61⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 61 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 61 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 61 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 61 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 61 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 61 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 61 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 61 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 61 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 61 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 61 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 61 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 61 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 61 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 61 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 61 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 61 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 61 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 61 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 61 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 61 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 61 (congrFun hsel 13)⟩

theorem raw_alias_cover_062 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 62) row), RawEnabled 62 g := by
  have hsel : rawSelections 62 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 87, 95, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 62 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 62⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 62⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 62⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 62⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 62⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 62⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 62⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 62⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 62⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 62⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 62⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 62⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 62⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 62⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 62⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 62⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 62⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 62⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 62⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 62⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 62 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 62 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 62 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 62 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 62 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 62 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 62 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 62 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 62 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 62 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 62 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 62 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 62 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 62 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 62 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 62 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 62 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 62 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 62 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 62 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 62 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 62 (congrFun hsel 13)⟩

theorem raw_alias_cover_063 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 63) row), RawEnabled 63 g := by
  have hsel : rawSelections 63 = (![7, 12, 22, 29, 35, 41, 50, 61, 69, 77, 87, 95, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 63 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 63⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 63⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 63⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 63⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 63⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 63⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 63⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 63⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 63⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 63⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 63⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 63⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 63⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 63⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 63⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 63⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 63⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 63⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 63⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 63⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 63 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 63 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 63 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 63 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 63 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 63 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 63 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 63 (congrFun hsel 5)⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 63 (congrFun hsel 6)⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 63 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 63 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 63 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 63 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 63 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 63 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 63 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 63 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 63 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 63 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 63 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 63 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 63 (congrFun hsel 13)⟩


end
end ElevenSquare.Tasks.T06
