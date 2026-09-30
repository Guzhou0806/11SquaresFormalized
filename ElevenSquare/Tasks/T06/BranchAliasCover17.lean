import ElevenSquare.Tasks.T06.BranchAliasFacts

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem raw_alias_cover_272 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 272) row), RawEnabled 272 g := by
  have hsel : rawSelections 272 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 83, 91, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 272 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 272⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 272⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 272⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 272⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 272⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 272⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 272⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 272⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 272⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 272⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 272⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 272⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 272⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 272⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 272⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 272⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 272⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 272⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 272⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 272⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 272 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 272 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 272 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 272 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 272 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 272 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 272 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 272 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 272 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 272 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 272 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 272 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 272 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 272 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 272 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 272 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 272 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 272 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 272 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 272 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 272 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 272 (congrFun hsel 13)⟩

theorem raw_alias_cover_273 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 273) row), RawEnabled 273 g := by
  have hsel : rawSelections 273 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 83, 91, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 273 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 273⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 273⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 273⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 273⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 273⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 273⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 273⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 273⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 273⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 273⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 273⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 273⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 273⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 273⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 273⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 273⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 273⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 273⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 273⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 273⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 273 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 273 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 273 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 273 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 273 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 273 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 273 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 273 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 273 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 273 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 273 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 273 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 273 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 273 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 273 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 273 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 273 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 273 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 273 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 273 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 273 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 273 (congrFun hsel 13)⟩

theorem raw_alias_cover_274 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 274) row), RawEnabled 274 g := by
  have hsel : rawSelections 274 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 83, 91, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 54, 55, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 274 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 274⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 274⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 274⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 274⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 274⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 274⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 274⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 274⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 274⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 274⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 274⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 274⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 274⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 274⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 274⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 274⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 274⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 274⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 274⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 274⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 274 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 274 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 274 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 274 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 274 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 274 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 274 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 274 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 274 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 274 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 274 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 274 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 274 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 274 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 274 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 274 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 274 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 274 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 274 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 274 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 274 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 274 (congrFun hsel 13)⟩

theorem raw_alias_cover_275 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 275) row), RawEnabled 275 g := by
  have hsel : rawSelections 275 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 83, 91, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 54, 55, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 275 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 275⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 275⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 275⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 275⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 275⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 275⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 275⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 275⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 275⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 275⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 275⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 275⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 275⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 275⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 275⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 275⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 275⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 275⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 275⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 275⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 275 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 275 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 275 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 275 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 275 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 275 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 275 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 275 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 275 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 275 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 275 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 275 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 275 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 275 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 275 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 275 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 275 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 275 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 275 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 275 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 275 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 275 (congrFun hsel 13)⟩

theorem raw_alias_cover_276 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 276) row), RawEnabled 276 g := by
  have hsel : rawSelections 276 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 83, 95, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 54, 55, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 276 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 276⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 276⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 276⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 276⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 276⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 276⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 276⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 276⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 276⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 276⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 276⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 276⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 276⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 276⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 276⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 276⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 276⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 276⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 276⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 276⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 276 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 276 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 276 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 276 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 276 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 276 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 276 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 276 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 276 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 276 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 276 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 276 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 276 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 276 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 276 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 276 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 276 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 276 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 276 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 276 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 276 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 276 (congrFun hsel 13)⟩

theorem raw_alias_cover_277 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 277) row), RawEnabled 277 g := by
  have hsel : rawSelections 277 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 83, 95, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 54, 55, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 277 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 277⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 277⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 277⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 277⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 277⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 277⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 277⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 277⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 277⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 277⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 277⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 277⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 277⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 277⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 277⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 277⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 277⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 277⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 277⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 277⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 277 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 277 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 277 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 277 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 277 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 277 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 277 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 277 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 277 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 277 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 277 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 277 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 277 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 277 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 277 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 277 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 277 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 277 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 277 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 277 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 277 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 277 (congrFun hsel 13)⟩

theorem raw_alias_cover_278 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 278) row), RawEnabled 278 g := by
  have hsel : rawSelections 278 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 83, 95, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 54, 55, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 278 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 278⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 278⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 278⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 278⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 278⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 278⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 278⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 278⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 278⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 278⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 278⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 278⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 278⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 278⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 278⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 278⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 278⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 278⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 278⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 278⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 278 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 278 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 278 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 278 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 278 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 278 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 278 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 278 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 278 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 278 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 278 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 278 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 278 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 278 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 278 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 278 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 278 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 278 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 278 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 278 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 278 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 278 (congrFun hsel 13)⟩

theorem raw_alias_cover_279 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 279) row), RawEnabled 279 g := by
  have hsel : rawSelections 279 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 83, 95, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 54, 55, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 279 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 279⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 279⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 279⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 279⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 279⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 279⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 279⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 279⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 279⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 279⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 279⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 279⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 279⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 279⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 279⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 279⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 279⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 279⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 279⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 279⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 279 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 279 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 279 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 279 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 279 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 279 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 279 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 279 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 279 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 279 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 279 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 279 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 279 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 279 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 279 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 279 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 279 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 279 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 279 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 279 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 279 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 279 (congrFun hsel 13)⟩

theorem raw_alias_cover_280 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 280) row), RawEnabled 280 g := by
  have hsel : rawSelections 280 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 87, 91, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 34, 35, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 280 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 280⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 280⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 280⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 280⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 280⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 280⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 280⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 280⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 280⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 280⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 280⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 280⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 280⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 280⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 280⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 280⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 280⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 280⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 280⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 280⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 280 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 280 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 280 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 280 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 280 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 280 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 280 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 280 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 280 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 280 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 280 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 280 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 280 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 280 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 280 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 280 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 280 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 280 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 280 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 280 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 280 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 280 (congrFun hsel 13)⟩

theorem raw_alias_cover_281 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 281) row), RawEnabled 281 g := by
  have hsel : rawSelections 281 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 87, 91, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 34, 35, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 281 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 281⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 281⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 281⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 281⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 281⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 281⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 281⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 281⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 281⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 281⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 281⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 281⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 281⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 281⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 281⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 281⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 281⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 281⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 281⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 281⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 281 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 281 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 281 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 281 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 281 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 281 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 281 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 281 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 281 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 281 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 281 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 281 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 281 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 281 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 281 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 281 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 281 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 281 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 281 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 281 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 281 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 281 (congrFun hsel 13)⟩

theorem raw_alias_cover_282 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 282) row), RawEnabled 282 g := by
  have hsel : rawSelections 282 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 87, 91, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 34, 35, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 282 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 282⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 282⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 282⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 282⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 282⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 282⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 282⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 282⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 282⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 282⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 282⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 282⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 282⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 282⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 282⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 282⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 282⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 282⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 282⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 282⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 282 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 282 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 282 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 282 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 282 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 282 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 282 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 282 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 282 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 282 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 282 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 282 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 282 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 282 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 282 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 282 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 282 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 282 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 282 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 282 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 282 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 282 (congrFun hsel 13)⟩

theorem raw_alias_cover_283 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 283) row), RawEnabled 283 g := by
  have hsel : rawSelections 283 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 87, 91, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 34, 35, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 283 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 283⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 283⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 283⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 283⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 283⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 283⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 283⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 283⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 283⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 283⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 283⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 283⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 283⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 283⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 283⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 283⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 283⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 283⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 283⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 283⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 283 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 283 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 283 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 283 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 283 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 283 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 283 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 283 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 283 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 283 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 283 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 283 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 283 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 283 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 283 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 283 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 283 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 283 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 283 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 283 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 283 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 283 (congrFun hsel 13)⟩

theorem raw_alias_cover_284 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 284) row), RawEnabled 284 g := by
  have hsel : rawSelections 284 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 87, 95, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 34, 35, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 284 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 284⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 284⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 284⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 284⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 284⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 284⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 284⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 284⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 284⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 284⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 284⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 284⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 284⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 284⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 284⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 284⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 284⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 284⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 284⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 284⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 284 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 284 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 284 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 284 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 284 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 284 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 284 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 284 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 284 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 284 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 284 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 284 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 284 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 284 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 284 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 284 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 284 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 284 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 284 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 284 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 284 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 284 (congrFun hsel 13)⟩

theorem raw_alias_cover_285 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 285) row), RawEnabled 285 g := by
  have hsel : rawSelections 285 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 87, 95, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 34, 35, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 285 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 285⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 285⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 285⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 285⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 285⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 285⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 285⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 285⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 285⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 285⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 285⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 285⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 285⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 285⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 285⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 285⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 285⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 285⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 285⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 285⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 285 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 285 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 285 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 285 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 285 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 285 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 285 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 285 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 285 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 285 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 285 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 285 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 285 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 285 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 285 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 285 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 285 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 285 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 285 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 285 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 285 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 285 (congrFun hsel 13)⟩

theorem raw_alias_cover_286 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 286) row), RawEnabled 286 g := by
  have hsel : rawSelections 286 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 87, 95, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 34, 35, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 286 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 286⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 286⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 286⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 286⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 286⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 286⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 286⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 286⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 286⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 286⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 286⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 286⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 286⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 286⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 286⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 286⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 286⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 286⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 286⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 286⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 286 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 286 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 286 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 286 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 286 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 286 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 286 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 286 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 286 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 286 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 286 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 286 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 286 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 286 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 286 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 286 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 286 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 286 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 286 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 286 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 286 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 286 (congrFun hsel 13)⟩

theorem raw_alias_cover_287 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 287) row), RawEnabled 287 g := by
  have hsel : rawSelections 287 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 77, 87, 95, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 287 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 287⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 287⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 287⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 287⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 287⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 287⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 287⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 287⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 287⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 287⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 287⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 287⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 287⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 287⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 287⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 287⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 287⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 287⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 287⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 287⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 287 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 287 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 287 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 287 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 287 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 287 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 287 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 287 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 287 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 287 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 287 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 287 (congrFun hsel 8)⟩
  · exact ⟨aliasGap52_0, aliasGap52_0_mem, aliasGap52_0_enabled 287 (congrFun hsel 9)⟩
  · exact ⟨aliasGap53_0, aliasGap53_0_mem, aliasGap53_0_enabled 287 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 287 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 287 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 287 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 287 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 287 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 287 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 287 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 287 (congrFun hsel 13)⟩


end
end ElevenSquare.Tasks.T06
