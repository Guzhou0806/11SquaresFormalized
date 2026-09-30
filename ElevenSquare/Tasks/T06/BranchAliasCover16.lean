import ElevenSquare.Tasks.T06.BranchAliasFacts

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem raw_alias_cover_256 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 256) row), RawEnabled 256 g := by
  have hsel : rawSelections 256 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 83, 91, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 256 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 256⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 256⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 256⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 256⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 256⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 256⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 256⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 256⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 256⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 256⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 256⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 256⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 256⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 256⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 256⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 256⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 256⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 256⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 256⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 256⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 256 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 256 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 256 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 256 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 256 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 256 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 256 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 256 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 256 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 256 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 256 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 256 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 256 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 256 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 256 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 256 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 256 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 256 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 256 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 256 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 256 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 256 (congrFun hsel 13)⟩

theorem raw_alias_cover_257 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 257) row), RawEnabled 257 g := by
  have hsel : rawSelections 257 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 83, 91, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 54, 55, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 257 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 257⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 257⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 257⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 257⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 257⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 257⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 257⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 257⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 257⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 257⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 257⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 257⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 257⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 257⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 257⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 257⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 257⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 257⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 257⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 257⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 257 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 257 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 257 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 257 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 257 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 257 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 257 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 257 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 257 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 257 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 257 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 257 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 257 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 257 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 257 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 257 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 257 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 257 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 257 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 257 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 257 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 257 (congrFun hsel 13)⟩

theorem raw_alias_cover_258 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 258) row), RawEnabled 258 g := by
  have hsel : rawSelections 258 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 83, 91, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 54, 55, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 258 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 258⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 258⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 258⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 258⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 258⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 258⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 258⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 258⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 258⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 258⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 258⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 258⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 258⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 258⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 258⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 258⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 258⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 258⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 258⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 258⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 258 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 258 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 258 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 258 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 258 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 258 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 258 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 258 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 258 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 258 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 258 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 258 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 258 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 258 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 258 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 258 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 258 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 258 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 258 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 258 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 258 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 258 (congrFun hsel 13)⟩

theorem raw_alias_cover_259 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 259) row), RawEnabled 259 g := by
  have hsel : rawSelections 259 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 83, 91, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 54, 55, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 259 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 259⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 259⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 259⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 259⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 259⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 259⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 259⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 259⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 259⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 259⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 259⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 259⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 259⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 259⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 259⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 259⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 259⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 259⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 259⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 259⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 259 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 259 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 259 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 259 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 259 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 259 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 259 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 259 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 259 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 259 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 259 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 259 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 259 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 259 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 259 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 259 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 259 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 259 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 259 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 259 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 259 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 259 (congrFun hsel 13)⟩

theorem raw_alias_cover_260 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 260) row), RawEnabled 260 g := by
  have hsel : rawSelections 260 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 83, 95, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 54, 55, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 260 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 260⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 260⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 260⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 260⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 260⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 260⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 260⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 260⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 260⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 260⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 260⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 260⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 260⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 260⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 260⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 260⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 260⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 260⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 260⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 260⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 260 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 260 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 260 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 260 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 260 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 260 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 260 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 260 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 260 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 260 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 260 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 260 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 260 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 260 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 260 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 260 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 260 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 260 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 260 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 260 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 260 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 260 (congrFun hsel 13)⟩

theorem raw_alias_cover_261 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 261) row), RawEnabled 261 g := by
  have hsel : rawSelections 261 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 83, 95, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 54, 55, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 261 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 261⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 261⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 261⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 261⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 261⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 261⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 261⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 261⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 261⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 261⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 261⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 261⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 261⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 261⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 261⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 261⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 261⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 261⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 261⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 261⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 261 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 261 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 261 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 261 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 261 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 261 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 261 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 261 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 261 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 261 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 261 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 261 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 261 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 261 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 261 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 261 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 261 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 261 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 261 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 261 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 261 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 261 (congrFun hsel 13)⟩

theorem raw_alias_cover_262 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 262) row), RawEnabled 262 g := by
  have hsel : rawSelections 262 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 83, 95, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 54, 55, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 262 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 262⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 262⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 262⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 262⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 262⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 262⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 262⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 262⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 262⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 262⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 262⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 262⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 262⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 262⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 262⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 262⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 262⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 262⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 262⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 262⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 262 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 262 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 262 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 262 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 262 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 262 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 262 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 262 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 262 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 262 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 262 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 262 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 262 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 262 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 262 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 262 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 262 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 262 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 262 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 262 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 262 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 262 (congrFun hsel 13)⟩

theorem raw_alias_cover_263 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 263) row), RawEnabled 263 g := by
  have hsel : rawSelections 263 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 83, 95, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 54, 55, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 263 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 263⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 263⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 263⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 263⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 263⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 263⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 263⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 263⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 263⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 263⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 263⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 263⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 263⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 263⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 263⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 263⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 263⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 263⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 263⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 263⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 263 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 263 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 263 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 263 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 263 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 263 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 263 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 263 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 263 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 263 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 263 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 263 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 263 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 263 (congrFun hsel 9)⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 263 (congrFun hsel 10)⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 263 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 263 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 263 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 263 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 263 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 263 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 263 (congrFun hsel 13)⟩

theorem raw_alias_cover_264 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 264) row), RawEnabled 264 g := by
  have hsel : rawSelections 264 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 87, 91, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 264 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 264⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 264⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 264⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 264⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 264⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 264⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 264⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 264⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 264⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 264⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 264⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 264⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 264⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 264⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 264⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 264⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 264⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 264⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 264⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 264⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 264 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 264 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 264 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 264 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 264 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 264 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 264 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 264 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 264 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 264 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 264 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 264 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 264 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 264 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 264 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 264 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 264 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 264 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 264 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 264 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 264 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 264 (congrFun hsel 13)⟩

theorem raw_alias_cover_265 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 265) row), RawEnabled 265 g := by
  have hsel : rawSelections 265 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 87, 91, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 265 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 265⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 265⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 265⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 265⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 265⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 265⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 265⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 265⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 265⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 265⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 265⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 265⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 265⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 265⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 265⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 265⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 265⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 265⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 265⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 265⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 265 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 265 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 265 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 265 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 265 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 265 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 265 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 265 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 265 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 265 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 265 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 265 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 265 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 265 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 265 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 265 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 265 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 265 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 265 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 265 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 265 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 265 (congrFun hsel 13)⟩

theorem raw_alias_cover_266 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 266) row), RawEnabled 266 g := by
  have hsel : rawSelections 266 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 87, 91, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 266 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 266⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 266⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 266⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 266⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 266⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 266⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 266⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 266⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 266⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 266⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 266⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 266⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 266⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 266⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 266⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 266⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 266⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 266⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 266⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 266⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 266 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 266 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 266 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 266 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 266 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 266 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 266 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 266 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 266 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 266 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 266 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 266 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 266 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 266 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 266 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 266 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 266 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 266 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 266 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 266 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 266 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 266 (congrFun hsel 13)⟩

theorem raw_alias_cover_267 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 267) row), RawEnabled 267 g := by
  have hsel : rawSelections 267 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 87, 91, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 267 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 267⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 267⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 267⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 267⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 267⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 267⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 267⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 267⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 267⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 267⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 267⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 267⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 267⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 267⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 267⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 267⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 267⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 267⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 267⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 267⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 267 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 267 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 267 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 267 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 267 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 267 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 267 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 267 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 267 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 267 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 267 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 267 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 267 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 267 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 267 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 267 (congrFun hsel 10)⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 267 (congrFun hsel 11)⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 267 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 267 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 267 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 267 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 267 (congrFun hsel 13)⟩

theorem raw_alias_cover_268 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 268) row), RawEnabled 268 g := by
  have hsel : rawSelections 268 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 87, 95, 97, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 268 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 268⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 268⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 268⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 268⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 268⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 268⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 268⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 268⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 268⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 268⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 268⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 268⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 268⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 268⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 268⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 268⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 268⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 268⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 268⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 268⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 268 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 268 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 268 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 268 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 268 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 268 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 268 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 268 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 268 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 268 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 268 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 268 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 268 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 268 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 268 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 268 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 268 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 268 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 268 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 268 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 268 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 268 (congrFun hsel 13)⟩

theorem raw_alias_cover_269 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 269) row), RawEnabled 269 g := by
  have hsel : rawSelections 269 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 87, 95, 97, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 269 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 269⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 269⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 269⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 269⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 269⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 269⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 269⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 269⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 269⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 269⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 269⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 269⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 269⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 269⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 269⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 269⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 269⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 269⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 269⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 269⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 269 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 269 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 269 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 269 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 269 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 269 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 269 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 269 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 269 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 269 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 269 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 269 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 269 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 269 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 269 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 269 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 269 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 269 (congrFun hsel 11)⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 269 (congrFun hsel 12)⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 269 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 269 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 269 (congrFun hsel 13)⟩

theorem raw_alias_cover_270 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 270) row), RawEnabled 270 g := by
  have hsel : rawSelections 270 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 87, 95, 101, 107] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) row), RawEnabled 270 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 270⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 270⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 270⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 270⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 270⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 270⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 270⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 270⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 270⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 270⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 270⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 270⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 270⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 270⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 270⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 270⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 270⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 270⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 270⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 270⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 270 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 270 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 270 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 270 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 270 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 270 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 270 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 270 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 270 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 270 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 270 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 270 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 270 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 270 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 270 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 270 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 270 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 270 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 270 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 270 (congrFun hsel 12)⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 270 (congrFun hsel 13)⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 270 (congrFun hsel 13)⟩

theorem raw_alias_cover_271 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 271) row), RawEnabled 271 g := by
  have hsel : rawSelections 271 = (![7, 12, 22, 29, 39, 41, 49, 61, 69, 73, 87, 95, 101, 111] : Fin 14 → Fin 112) := rfl
  change ∃ g ∈ rowAliases ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) row), RawEnabled 271 g
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 271⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 271⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 271⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 271⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 271⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 271⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 271⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 271⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 271⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 271⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 271⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 271⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 271⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 271⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 271⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 271⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 271⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 271⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 271⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 271⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 271 (congrFun hsel 0)⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 271 (congrFun hsel 1)⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 271 (congrFun hsel 2)⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 271 (congrFun hsel 3)⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 271 (congrFun hsel 4)⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 271 (congrFun hsel 4)⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 271 (congrFun hsel 5)⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 271 (congrFun hsel 5)⟩
  · exact ⟨aliasGap28_0, aliasGap28_0_mem, aliasGap28_0_enabled 271 (congrFun hsel 6)⟩
  · exact ⟨aliasGap29_0, aliasGap29_0_mem, aliasGap29_0_enabled 271 (congrFun hsel 6)⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 271 (congrFun hsel 7)⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 271 (congrFun hsel 8)⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 271 (congrFun hsel 9)⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 271 (congrFun hsel 9)⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 271 (congrFun hsel 10)⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 271 (congrFun hsel 10)⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 271 (congrFun hsel 11)⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 271 (congrFun hsel 11)⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 271 (congrFun hsel 12)⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 271 (congrFun hsel 12)⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 271 (congrFun hsel 13)⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 271 (congrFun hsel 13)⟩


end
end ElevenSquare.Tasks.T06
