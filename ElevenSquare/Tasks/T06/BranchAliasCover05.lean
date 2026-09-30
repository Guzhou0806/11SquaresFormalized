import ElevenSquare.Tasks.T06.BranchAliasFacts

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem raw_alias_cover_080 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 80) row), RawEnabled 80 g := by
  have hsel : rawSelections 80 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 83, 91, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 80 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 80⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 80⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 80⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 80⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 80⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 80⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 80⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 80⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 80⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 80⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 80⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 80⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 80⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 80⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 80⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 80⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 80⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 80⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 80⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 80⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 80 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 80 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 80 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 80 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 80 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 80 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 80 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 80 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 80 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 80 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 80 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 80 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 80 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 80 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 80 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 80 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 80 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 80 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 80 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 80 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 80 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 80 (congrFun hsel 13)⟩

theorem raw_alias_cover_081 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 81) row), RawEnabled 81 g := by
  have hsel : rawSelections 81 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 83, 91, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 81 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 81⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 81⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 81⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 81⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 81⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 81⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 81⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 81⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 81⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 81⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 81⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 81⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 81⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 81⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 81⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 81⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 81⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 81⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 81⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 81⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 81 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 81 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 81 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 81 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 81 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 81 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 81 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 81 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 81 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 81 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 81 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 81 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 81 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 81 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 81 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 81 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 81 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 81 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 81 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 81 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 81 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 81 (congrFun hsel 13)⟩

theorem raw_alias_cover_082 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 82) row), RawEnabled 82 g := by
  have hsel : rawSelections 82 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 83, 91, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 54, 55, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 82 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 82⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 82⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 82⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 82⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 82⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 82⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 82⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 82⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 82⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 82⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 82⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 82⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 82⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 82⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 82⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 82⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 82⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 82⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 82⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 82⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 82 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 82 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 82 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 82 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 82 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 82 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 82 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 82 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 82 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 82 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 82 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 82 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 82 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 82 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 82 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 82 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 82 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 82 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 82 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 82 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 82 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 82 (congrFun hsel 13)⟩

theorem raw_alias_cover_083 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 83) row), RawEnabled 83 g := by
  have hsel : rawSelections 83 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 83, 91, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 54, 55, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 83 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 83⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 83⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 83⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 83⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 83⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 83⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 83⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 83⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 83⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 83⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 83⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 83⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 83⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 83⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 83⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 83⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 83⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 83⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 83⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 83⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 83 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 83 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 83 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 83 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 83 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 83 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 83 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 83 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 83 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 83 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 83 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 83 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 83 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 83 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 83 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 83 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 83 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 83 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 83 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 83 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 83 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 83 (congrFun hsel 13)⟩

theorem raw_alias_cover_084 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 84) row), RawEnabled 84 g := by
  have hsel : rawSelections 84 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 83, 95, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 54, 55, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 84 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 84⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 84⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 84⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 84⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 84⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 84⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 84⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 84⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 84⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 84⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 84⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 84⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 84⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 84⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 84⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 84⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 84⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 84⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 84⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 84⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 84 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 84 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 84 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 84 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 84 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 84 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 84 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 84 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 84 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 84 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 84 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 84 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 84 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 84 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 84 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 84 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 84 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 84 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 84 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 84 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 84 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 84 (congrFun hsel 13)⟩

theorem raw_alias_cover_085 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 85) row), RawEnabled 85 g := by
  have hsel : rawSelections 85 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 83, 95, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 54, 55, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 85 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 85⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 85⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 85⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 85⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 85⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 85⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 85⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 85⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 85⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 85⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 85⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 85⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 85⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 85⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 85⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 85⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 85⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 85⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 85⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 85⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 85 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 85 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 85 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 85 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 85 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 85 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 85 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 85 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 85 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 85 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 85 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 85 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 85 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 85 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 85 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 85 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 85 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 85 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 85 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 85 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 85 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 85 (congrFun hsel 13)⟩

theorem raw_alias_cover_086 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 86) row), RawEnabled 86 g := by
  have hsel : rawSelections 86 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 83, 95, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 54, 55, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 86 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 86⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 86⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 86⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 86⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 86⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 86⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 86⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 86⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 86⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 86⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 86⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 86⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 86⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 86⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 86⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 86⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 86⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 86⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 86⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 86⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 86 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 86 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 86 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 86 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 86 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 86 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 86 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 86 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 86 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 86 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 86 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 86 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 86 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 86 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 86 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 86 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 86 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 86 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 86 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 86 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 86 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 86 (congrFun hsel 13)⟩

theorem raw_alias_cover_087 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 87) row), RawEnabled 87 g := by
  have hsel : rawSelections 87 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 83, 95, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 54, 55, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 87 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 87⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 87⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 87⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 87⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 87⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 87⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 87⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 87⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 87⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 87⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 87⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 87⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 87⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 87⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 87⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 87⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 87⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 87⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 87⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 87⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 87 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 87 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 87 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 87 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 87 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 87 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 87 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 87 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 87 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 87 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 87 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 87 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 87 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 87 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 87 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 87 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 87 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 87 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 87 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 87 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 87 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 87 (congrFun hsel 13)⟩

theorem raw_alias_cover_088 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 88) row), RawEnabled 88 g := by
  have hsel : rawSelections 88 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 87, 91, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 88 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 88⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 88⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 88⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 88⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 88⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 88⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 88⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 88⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 88⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 88⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 88⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 88⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 88⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 88⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 88⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 88⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 88⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 88⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 88⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 88⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 88 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 88 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 88 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 88 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 88 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 88 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 88 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 88 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 88 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 88 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 88 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 88 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 88 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 88 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 88 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 88 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 88 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 88 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 88 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 88 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 88 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 88 (congrFun hsel 13)⟩

theorem raw_alias_cover_089 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 89) row), RawEnabled 89 g := by
  have hsel : rawSelections 89 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 87, 91, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 89 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 89⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 89⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 89⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 89⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 89⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 89⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 89⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 89⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 89⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 89⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 89⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 89⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 89⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 89⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 89⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 89⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 89⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 89⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 89⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 89⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 89 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 89 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 89 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 89 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 89 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 89 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 89 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 89 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 89 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 89 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 89 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 89 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 89 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 89 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 89 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 89 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 89 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 89 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 89 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 89 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 89 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 89 (congrFun hsel 13)⟩

theorem raw_alias_cover_090 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 90) row), RawEnabled 90 g := by
  have hsel : rawSelections 90 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 87, 91, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 90 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 90⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 90⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 90⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 90⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 90⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 90⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 90⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 90⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 90⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 90⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 90⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 90⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 90⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 90⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 90⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 90⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 90⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 90⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 90⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 90⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 90 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 90 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 90 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 90 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 90 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 90 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 90 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 90 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 90 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 90 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 90 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 90 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 90 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 90 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 90 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 90 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 90 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 90 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 90 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 90 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 90 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 90 (congrFun hsel 13)⟩

theorem raw_alias_cover_091 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 91) row), RawEnabled 91 g := by
  have hsel : rawSelections 91 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 87, 91, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 91 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 91⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 91⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 91⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 91⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 91⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 91⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 91⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 91⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 91⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 91⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 91⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 91⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 91⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 91⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 91⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 91⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 91⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 91⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 91⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 91⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 91 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 91 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 91 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 91 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 91 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 91 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 91 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 91 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 91 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 91 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 91 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 91 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 91 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 91 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 91 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 91 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 91 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 91 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 91 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 91 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 91 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 91 (congrFun hsel 13)⟩

theorem raw_alias_cover_092 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 92) row), RawEnabled 92 g := by
  have hsel : rawSelections 92 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 87, 95, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 92 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 92⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 92⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 92⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 92⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 92⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 92⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 92⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 92⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 92⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 92⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 92⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 92⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 92⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 92⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 92⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 92⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 92⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 92⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 92⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 92⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 92 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 92 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 92 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 92 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 92 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 92 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 92 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 92 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 92 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 92 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 92 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 92 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 92 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 92 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 92 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 92 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 92 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 92 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 92 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 92 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 92 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 92 (congrFun hsel 13)⟩

theorem raw_alias_cover_093 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 93) row), RawEnabled 93 g := by
  have hsel : rawSelections 93 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 87, 95, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 93 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 93⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 93⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 93⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 93⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 93⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 93⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 93⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 93⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 93⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 93⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 93⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 93⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 93⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 93⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 93⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 93⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 93⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 93⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 93⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 93⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 93 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 93 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 93 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 93 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 93 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 93 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 93 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 93 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 93 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 93 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 93 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 93 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 93 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 93 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 93 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 93 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 93 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 93 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 93 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 93 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 93 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 93 (congrFun hsel 13)⟩

theorem raw_alias_cover_094 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 94) row), RawEnabled 94 g := by
  have hsel : rawSelections 94 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 87, 95, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 94 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 94⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 94⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 94⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 94⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 94⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 94⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 94⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 94⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 94⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 94⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 94⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 94⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 94⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 94⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 94⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 94⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 94⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 94⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 94⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 94⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 94 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 94 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 94 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 94 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 94 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 94 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 94 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 94 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 94 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 94 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 94 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 94 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 94 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 94 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 94 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 94 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 94 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 94 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 94 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 94 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 94 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 94 (congrFun hsel 13)⟩

theorem raw_alias_cover_095 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 95) row), RawEnabled 95 g := by
  have hsel : rawSelections 95 = (![7, 12, 22, 29, 35, 41, 53, 61, 69, 77, 87, 95, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 95 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 95⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 95⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 95⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 95⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 95⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 95⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 95⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 95⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 95⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 95⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 95⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 95⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 95⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 95⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 95⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 95⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 95⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 95⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 95⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 95⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 95 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 95 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 95 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 95 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_0, aliasGap24_0_mem, aliasGap24_0_enabled 95 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_0, aliasGap25_0_mem, aliasGap25_0_enabled 95 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 95 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 95 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_1, aliasGap28_1_mem, aliasGap28_1_enabled 95 (congrFun hsel 6)⟩
  · exact ⟨aliasGap42_0, aliasGap42_0_mem, aliasGap42_0_enabled 95 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 95 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 95 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 95 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 95 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 95 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 95 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 95 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 95 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 95 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 95 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 95 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 95 (congrFun hsel 13)⟩


end
end ElevenSquare.Tasks.T06
