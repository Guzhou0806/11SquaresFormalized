import ElevenSquare.Tasks.T06.BranchAliasFacts

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem raw_alias_cover_480 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 480) row), RawEnabled 480 g := by
  have hsel : rawSelections 480 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 83, 91, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 480 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 480⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 480⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 480⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 480⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 480⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 480⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 480⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 480⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 480⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 480⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 480⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 480⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 480⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 480⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 480⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 480⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 480⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 480⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 480⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 480⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 480 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 480 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 480 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 480 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 480 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 480 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 480 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 480 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 480 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 480 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 480 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 480 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 480 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 480 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 480 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 480 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 480 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 480 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 480 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 480 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 480 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 480 (congrFun hsel 13)⟩

theorem raw_alias_cover_481 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 481) row), RawEnabled 481 g := by
  have hsel : rawSelections 481 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 83, 91, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 54, 55, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 481 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 481⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 481⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 481⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 481⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 481⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 481⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 481⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 481⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 481⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 481⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 481⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 481⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 481⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 481⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 481⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 481⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 481⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 481⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 481⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 481⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 481 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 481 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 481 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 481 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 481 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 481 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 481 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 481 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 481 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 481 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 481 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 481 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 481 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 481 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 481 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 481 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 481 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 481 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 481 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 481 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 481 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 481 (congrFun hsel 13)⟩

theorem raw_alias_cover_482 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 482) row), RawEnabled 482 g := by
  have hsel : rawSelections 482 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 83, 91, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 54, 55, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 482 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 482⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 482⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 482⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 482⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 482⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 482⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 482⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 482⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 482⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 482⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 482⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 482⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 482⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 482⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 482⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 482⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 482⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 482⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 482⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 482⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 482 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 482 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 482 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 482 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 482 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 482 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 482 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 482 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 482 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 482 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 482 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 482 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 482 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 482 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 482 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 482 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 482 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 482 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 482 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 482 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 482 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 482 (congrFun hsel 13)⟩

theorem raw_alias_cover_483 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 483) row), RawEnabled 483 g := by
  have hsel : rawSelections 483 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 83, 91, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 54, 55, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 483 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 483⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 483⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 483⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 483⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 483⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 483⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 483⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 483⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 483⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 483⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 483⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 483⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 483⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 483⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 483⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 483⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 483⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 483⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 483⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 483⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 483 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 483 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 483 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 483 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 483 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 483 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 483 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 483 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 483 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 483 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 483 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 483 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 483 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 483 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 483 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 483 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 483 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 483 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 483 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 483 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 483 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 483 (congrFun hsel 13)⟩

theorem raw_alias_cover_484 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 484) row), RawEnabled 484 g := by
  have hsel : rawSelections 484 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 83, 95, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 54, 55, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 484 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 484⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 484⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 484⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 484⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 484⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 484⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 484⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 484⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 484⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 484⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 484⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 484⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 484⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 484⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 484⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 484⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 484⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 484⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 484⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 484⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 484 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 484 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 484 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 484 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 484 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 484 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 484 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 484 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 484 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 484 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 484 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 484 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 484 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 484 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 484 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 484 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 484 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 484 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 484 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 484 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 484 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 484 (congrFun hsel 13)⟩

theorem raw_alias_cover_485 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 485) row), RawEnabled 485 g := by
  have hsel : rawSelections 485 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 83, 95, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 54, 55, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 485 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 485⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 485⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 485⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 485⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 485⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 485⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 485⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 485⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 485⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 485⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 485⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 485⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 485⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 485⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 485⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 485⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 485⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 485⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 485⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 485⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 485 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 485 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 485 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 485 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 485 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 485 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 485 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 485 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 485 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 485 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 485 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 485 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 485 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 485 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 485 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 485 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 485 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 485 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 485 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 485 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 485 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 485 (congrFun hsel 13)⟩

theorem raw_alias_cover_486 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 486) row), RawEnabled 486 g := by
  have hsel : rawSelections 486 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 83, 95, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 54, 55, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 486 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 486⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 486⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 486⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 486⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 486⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 486⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 486⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 486⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 486⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 486⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 486⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 486⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 486⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 486⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 486⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 486⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 486⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 486⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 486⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 486⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 486 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 486 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 486 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 486 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 486 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 486 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 486 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 486 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 486 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 486 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 486 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 486 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 486 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 486 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 486 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 486 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 486 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 486 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 486 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 486 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 486 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 486 (congrFun hsel 13)⟩

theorem raw_alias_cover_487 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 487) row), RawEnabled 487 g := by
  have hsel : rawSelections 487 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 83, 95, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 54, 55, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 487 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 487⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 487⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 487⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 487⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 487⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 487⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 487⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 487⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 487⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 487⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 487⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 487⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 487⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 487⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 487⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 487⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 487⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 487⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 487⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 487⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 487 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 487 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 487 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 487 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 487 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 487 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 487 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 487 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 487 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 487 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 487 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 487 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 487 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 487 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 487 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 487 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 487 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 487 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 487 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 487 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 487 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 487 (congrFun hsel 13)⟩

theorem raw_alias_cover_488 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 488) row), RawEnabled 488 g := by
  have hsel : rawSelections 488 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 87, 91, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 488 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 488⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 488⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 488⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 488⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 488⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 488⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 488⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 488⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 488⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 488⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 488⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 488⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 488⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 488⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 488⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 488⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 488⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 488⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 488⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 488⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 488 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 488 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 488 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 488 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 488 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 488 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 488 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 488 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 488 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 488 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 488 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 488 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 488 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 488 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 488 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 488 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 488 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 488 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 488 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 488 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 488 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 488 (congrFun hsel 13)⟩

theorem raw_alias_cover_489 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 489) row), RawEnabled 489 g := by
  have hsel : rawSelections 489 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 87, 91, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 489 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 489⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 489⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 489⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 489⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 489⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 489⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 489⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 489⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 489⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 489⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 489⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 489⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 489⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 489⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 489⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 489⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 489⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 489⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 489⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 489⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 489 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 489 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 489 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 489 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 489 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 489 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 489 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 489 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 489 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 489 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 489 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 489 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 489 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 489 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 489 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 489 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 489 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 489 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 489 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 489 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 489 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 489 (congrFun hsel 13)⟩

theorem raw_alias_cover_490 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 490) row), RawEnabled 490 g := by
  have hsel : rawSelections 490 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 87, 91, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 490 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 490⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 490⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 490⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 490⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 490⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 490⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 490⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 490⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 490⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 490⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 490⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 490⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 490⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 490⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 490⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 490⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 490⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 490⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 490⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 490⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 490 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 490 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 490 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 490 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 490 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 490 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 490 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 490 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 490 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 490 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 490 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 490 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 490 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 490 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 490 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 490 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 490 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 490 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 490 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 490 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 490 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 490 (congrFun hsel 13)⟩

theorem raw_alias_cover_491 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 491) row), RawEnabled 491 g := by
  have hsel : rawSelections 491 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 87, 91, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 491 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 491⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 491⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 491⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 491⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 491⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 491⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 491⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 491⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 491⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 491⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 491⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 491⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 491⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 491⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 491⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 491⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 491⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 491⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 491⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 491⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 491 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 491 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 491 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 491 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 491 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 491 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 491 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 491 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 491 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 491 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 491 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 491 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 491 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 491 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 491 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 491 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 491 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 491 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 491 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 491 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 491 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 491 (congrFun hsel 13)⟩

theorem raw_alias_cover_492 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 492) row), RawEnabled 492 g := by
  have hsel : rawSelections 492 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 87, 95, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 492 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 492⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 492⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 492⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 492⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 492⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 492⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 492⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 492⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 492⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 492⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 492⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 492⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 492⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 492⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 492⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 492⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 492⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 492⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 492⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 492⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 492 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 492 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 492 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 492 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 492 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 492 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 492 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 492 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 492 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 492 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 492 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 492 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 492 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 492 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 492 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 492 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 492 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 492 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 492 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 492 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 492 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 492 (congrFun hsel 13)⟩

theorem raw_alias_cover_493 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 493) row), RawEnabled 493 g := by
  have hsel : rawSelections 493 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 87, 95, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 493 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 493⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 493⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 493⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 493⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 493⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 493⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 493⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 493⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 493⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 493⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 493⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 493⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 493⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 493⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 493⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 493⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 493⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 493⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 493⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 493⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 493 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 493 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 493 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 493 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 493 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 493 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 493 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 493 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 493 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 493 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 493 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 493 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 493 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 493 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 493 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 493 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 493 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 493 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 493 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 493 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 493 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 493 (congrFun hsel 13)⟩

theorem raw_alias_cover_494 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 494) row), RawEnabled 494 g := by
  have hsel : rawSelections 494 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 87, 95, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 494 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 494⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 494⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 494⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 494⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 494⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 494⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 494⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 494⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 494⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 494⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 494⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 494⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 494⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 494⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 494⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 494⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 494⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 494⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 494⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 494⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 494 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 494 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 494 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 494 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 494 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 494 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 494 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 494 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 494 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 494 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 494 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 494 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 494 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 494 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 494 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 494 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 494 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 494 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 494 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 494 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 494 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 494 (congrFun hsel 13)⟩

theorem raw_alias_cover_495 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 495) row), RawEnabled 495 g := by
  have hsel : rawSelections 495 = (![7, 12, 22, 29, 39, 45, 54, 61, 69, 73, 87, 95, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 495 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 495⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 495⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 495⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 495⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 495⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 495⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 495⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 495⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 495⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 495⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 495⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 495⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 495⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 495⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 495⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 495⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 495⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 495⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 495⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 495⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 495 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 495 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 495 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 495 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 495 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 495 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_1, aliasGap26_1_mem, aliasGap26_1_enabled 495 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_1, aliasGap27_1_mem, aliasGap27_1_enabled 495 (congrFun hsel 5)⟩
  · exact ⟨aliasGap43_1, aliasGap43_1_mem, aliasGap43_1_enabled 495 (congrFun hsel 6)⟩
  · exact ⟨aliasGap44_0, aliasGap44_0_mem, aliasGap44_0_enabled 495 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 495 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 495 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 495 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 495 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 495 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 495 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 495 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 495 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 495 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 495 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 495 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 495 (congrFun hsel 13)⟩


end
end ElevenSquare.Tasks.T06
