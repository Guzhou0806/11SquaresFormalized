import ElevenSquare.Tasks.T06.BranchAliasFacts

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem raw_alias_cover_288 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 288) row), RawEnabled 288 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 288⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 288⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 288⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 288⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 288⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 288⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 288⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 288⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 288⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 288⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 288⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 288⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 288⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 288⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 288⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 288⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 288⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 288⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 288⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 288⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 288 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 288 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 288 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 288 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 288 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 288 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 288 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 288 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 288 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 288 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 288 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 288 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 288 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 288 rfl⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 288 rfl⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 288 rfl⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 288 rfl⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 288 rfl⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 288 rfl⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 288 rfl⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 288 rfl⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 288 rfl⟩

theorem raw_alias_cover_289 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 289) row), RawEnabled 289 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 289⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 289⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 289⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 289⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 289⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 289⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 289⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 289⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 289⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 289⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 289⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 289⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 289⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 289⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 289⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 289⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 289⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 289⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 289⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 289⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 289 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 289 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 289 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 289 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 289 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 289 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 289 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 289 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 289 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 289 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 289 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 289 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 289 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 289 rfl⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 289 rfl⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 289 rfl⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 289 rfl⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 289 rfl⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 289 rfl⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 289 rfl⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 289 rfl⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 289 rfl⟩

theorem raw_alias_cover_290 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 290) row), RawEnabled 290 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 290⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 290⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 290⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 290⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 290⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 290⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 290⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 290⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 290⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 290⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 290⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 290⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 290⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 290⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 290⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 290⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 290⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 290⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 290⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 290⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 290 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 290 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 290 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 290 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 290 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 290 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 290 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 290 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 290 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 290 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 290 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 290 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 290 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 290 rfl⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 290 rfl⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 290 rfl⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 290 rfl⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 290 rfl⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 290 rfl⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 290 rfl⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 290 rfl⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 290 rfl⟩

theorem raw_alias_cover_291 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 291) row), RawEnabled 291 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 291⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 291⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 291⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 291⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 291⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 291⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 291⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 291⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 291⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 291⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 291⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 291⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 291⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 291⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 291⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 291⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 291⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 291⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 291⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 291⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 291 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 291 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 291 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 291 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 291 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 291 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 291 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 291 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 291 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 291 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 291 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 291 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 291 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 291 rfl⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 291 rfl⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 291 rfl⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 291 rfl⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 291 rfl⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 291 rfl⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 291 rfl⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 291 rfl⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 291 rfl⟩

theorem raw_alias_cover_292 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 292) row), RawEnabled 292 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 292⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 292⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 292⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 292⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 292⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 292⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 292⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 292⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 292⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 292⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 292⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 292⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 292⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 292⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 292⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 292⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 292⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 292⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 292⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 292⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 292 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 292 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 292 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 292 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 292 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 292 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 292 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 292 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 292 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 292 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 292 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 292 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 292 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 292 rfl⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 292 rfl⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 292 rfl⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 292 rfl⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 292 rfl⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 292 rfl⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 292 rfl⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 292 rfl⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 292 rfl⟩

theorem raw_alias_cover_293 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 293) row), RawEnabled 293 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 293⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 293⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 293⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 293⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 293⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 293⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 293⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 293⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 293⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 293⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 293⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 293⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 293⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 293⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 293⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 293⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 293⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 293⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 293⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 293⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 293 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 293 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 293 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 293 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 293 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 293 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 293 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 293 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 293 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 293 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 293 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 293 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 293 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 293 rfl⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 293 rfl⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 293 rfl⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 293 rfl⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 293 rfl⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 293 rfl⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 293 rfl⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 293 rfl⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 293 rfl⟩

theorem raw_alias_cover_294 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 294) row), RawEnabled 294 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 294⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 294⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 294⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 294⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 294⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 294⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 294⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 294⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 294⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 294⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 294⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 294⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 294⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 294⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 294⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 294⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 294⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 294⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 294⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 294⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 294 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 294 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 294 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 294 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 294 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 294 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 294 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 294 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 294 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 294 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 294 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 294 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 294 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 294 rfl⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 294 rfl⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 294 rfl⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 294 rfl⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 294 rfl⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 294 rfl⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 294 rfl⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 294 rfl⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 294 rfl⟩

theorem raw_alias_cover_295 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 295) row), RawEnabled 295 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 295⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 295⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 295⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 295⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 295⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 295⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 295⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 295⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 295⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 295⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 295⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 295⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 295⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 295⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 295⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 295⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 295⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 295⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 295⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 295⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 295 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 295 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 295 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 295 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 295 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 295 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 295 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 295 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 295 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 295 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 295 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 295 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 295 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 295 rfl⟩
  · exact ⟨aliasGap54_0, aliasGap54_0_mem, aliasGap54_0_enabled 295 rfl⟩
  · exact ⟨aliasGap55_0, aliasGap55_0_mem, aliasGap55_0_enabled 295 rfl⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 295 rfl⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 295 rfl⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 295 rfl⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 295 rfl⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 295 rfl⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 295 rfl⟩

theorem raw_alias_cover_296 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 296) row), RawEnabled 296 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 296⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 296⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 296⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 296⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 296⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 296⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 296⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 296⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 296⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 296⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 296⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 296⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 296⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 296⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 296⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 296⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 296⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 296⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 296⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 296⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 296 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 296 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 296 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 296 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 296 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 296 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 296 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 296 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 296 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 296 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 296 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 296 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 296 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 296 rfl⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 296 rfl⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 296 rfl⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 296 rfl⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 296 rfl⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 296 rfl⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 296 rfl⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 296 rfl⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 296 rfl⟩

theorem raw_alias_cover_297 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 297) row), RawEnabled 297 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 297⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 297⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 297⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 297⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 297⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 297⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 297⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 297⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 297⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 297⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 297⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 297⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 297⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 297⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 297⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 297⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 297⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 297⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 297⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 297⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 297 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 297 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 297 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 297 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 297 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 297 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 297 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 297 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 297 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 297 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 297 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 297 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 297 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 297 rfl⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 297 rfl⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 297 rfl⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 297 rfl⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 297 rfl⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 297 rfl⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 297 rfl⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 297 rfl⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 297 rfl⟩

theorem raw_alias_cover_298 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 298) row), RawEnabled 298 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 298⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 298⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 298⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 298⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 298⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 298⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 298⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 298⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 298⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 298⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 298⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 298⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 298⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 298⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 298⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 298⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 298⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 298⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 298⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 298⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 298 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 298 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 298 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 298 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 298 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 298 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 298 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 298 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 298 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 298 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 298 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 298 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 298 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 298 rfl⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 298 rfl⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 298 rfl⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 298 rfl⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 298 rfl⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 298 rfl⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 298 rfl⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 298 rfl⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 298 rfl⟩

theorem raw_alias_cover_299 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 299) row), RawEnabled 299 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 299⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 299⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 299⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 299⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 299⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 299⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 299⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 299⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 299⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 299⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 299⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 299⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 299⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 299⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 299⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 299⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 299⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 299⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 299⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 299⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 299 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 299 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 299 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 299 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 299 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 299 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 299 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 299 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 299 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 299 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 299 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 299 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 299 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 299 rfl⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 299 rfl⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 299 rfl⟩
  · exact ⟨aliasGap50_0, aliasGap50_0_mem, aliasGap50_0_enabled 299 rfl⟩
  · exact ⟨aliasGap51_0, aliasGap51_0_mem, aliasGap51_0_enabled 299 rfl⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 299 rfl⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 299 rfl⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 299 rfl⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 299 rfl⟩

theorem raw_alias_cover_300 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 300) row), RawEnabled 300 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 300⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 300⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 300⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 300⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 300⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 300⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 300⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 300⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 300⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 300⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 300⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 300⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 300⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 300⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 300⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 300⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 300⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 300⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 300⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 300⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 300 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 300 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 300 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 300 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 300 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 300 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 300 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 300 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 300 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 300 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 300 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 300 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 300 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 300 rfl⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 300 rfl⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 300 rfl⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 300 rfl⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 300 rfl⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 300 rfl⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 300 rfl⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 300 rfl⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 300 rfl⟩

theorem raw_alias_cover_301 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 301) row), RawEnabled 301 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 301⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 301⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 301⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 301⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 301⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 301⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 301⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 301⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 301⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 301⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 301⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 301⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 301⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 301⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 301⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 301⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 301⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 301⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 301⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 301⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 301 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 301 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 301 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 301 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 301 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 301 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 301 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 301 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 301 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 301 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 301 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 301 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 301 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 301 rfl⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 301 rfl⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 301 rfl⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 301 rfl⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 301 rfl⟩
  · exact ⟨aliasGap38_0, aliasGap38_0_mem, aliasGap38_0_enabled 301 rfl⟩
  · exact ⟨aliasGap39_0, aliasGap39_0_mem, aliasGap39_0_enabled 301 rfl⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 301 rfl⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 301 rfl⟩

theorem raw_alias_cover_302 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 302) row), RawEnabled 302 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 302⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 302⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 302⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 302⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 302⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 302⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 302⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 302⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 302⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 302⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 302⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 302⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 302⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 302⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 302⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 302⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 302⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 302⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 302⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 302⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 302 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 302 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 302 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 302 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 302 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 302 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 302 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 302 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 302 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 302 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 302 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 302 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 302 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 302 rfl⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 302 rfl⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 302 rfl⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 302 rfl⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 302 rfl⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 302 rfl⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 302 rfl⟩
  · exact ⟨aliasGap40_0, aliasGap40_0_mem, aliasGap40_0_enabled 302 rfl⟩
  · exact ⟨aliasGap41_0, aliasGap41_0_mem, aliasGap41_0_enabled 302 rfl⟩

theorem raw_alias_cover_303 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 303) row), RawEnabled 303 g := by
  fin_cases row
  · exact ⟨aliasGap00_0, aliasGap00_0_mem, aliasGap00_0_enabled 303⟩
  · exact ⟨aliasGap01_0, aliasGap01_0_mem, aliasGap01_0_enabled 303⟩
  · exact ⟨aliasGap02_0, aliasGap02_0_mem, aliasGap02_0_enabled 303⟩
  · exact ⟨aliasGap03_0, aliasGap03_0_mem, aliasGap03_0_enabled 303⟩
  · exact ⟨aliasGap04_0, aliasGap04_0_mem, aliasGap04_0_enabled 303⟩
  · exact ⟨aliasGap05_0, aliasGap05_0_mem, aliasGap05_0_enabled 303⟩
  · exact ⟨aliasGap06_0, aliasGap06_0_mem, aliasGap06_0_enabled 303⟩
  · exact ⟨aliasGap07_0, aliasGap07_0_mem, aliasGap07_0_enabled 303⟩
  · exact ⟨aliasGap08_0, aliasGap08_0_mem, aliasGap08_0_enabled 303⟩
  · exact ⟨aliasGap09_0, aliasGap09_0_mem, aliasGap09_0_enabled 303⟩
  · exact ⟨aliasGap10_0, aliasGap10_0_mem, aliasGap10_0_enabled 303⟩
  · exact ⟨aliasGap11_0, aliasGap11_0_mem, aliasGap11_0_enabled 303⟩
  · exact ⟨aliasGap12_0, aliasGap12_0_mem, aliasGap12_0_enabled 303⟩
  · exact ⟨aliasGap13_0, aliasGap13_0_mem, aliasGap13_0_enabled 303⟩
  · exact ⟨aliasGap14_0, aliasGap14_0_mem, aliasGap14_0_enabled 303⟩
  · exact ⟨aliasGap15_0, aliasGap15_0_mem, aliasGap15_0_enabled 303⟩
  · exact ⟨aliasGap16_0, aliasGap16_0_mem, aliasGap16_0_enabled 303⟩
  · exact ⟨aliasGap17_0, aliasGap17_0_mem, aliasGap17_0_enabled 303⟩
  · exact ⟨aliasGap18_0, aliasGap18_0_mem, aliasGap18_0_enabled 303⟩
  · exact ⟨aliasGap19_0, aliasGap19_0_mem, aliasGap19_0_enabled 303⟩
  · exact ⟨aliasGap20_0, aliasGap20_0_mem, aliasGap20_0_enabled 303 rfl⟩
  · exact ⟨aliasGap21_0, aliasGap21_0_mem, aliasGap21_0_enabled 303 rfl⟩
  · exact ⟨aliasGap22_0, aliasGap22_0_mem, aliasGap22_0_enabled 303 rfl⟩
  · exact ⟨aliasGap23_0, aliasGap23_0_mem, aliasGap23_0_enabled 303 rfl⟩
  · exact ⟨aliasGap24_1, aliasGap24_1_mem, aliasGap24_1_enabled 303 rfl⟩
  · exact ⟨aliasGap25_1, aliasGap25_1_mem, aliasGap25_1_enabled 303 rfl⟩
  · exact ⟨aliasGap26_0, aliasGap26_0_mem, aliasGap26_0_enabled 303 rfl⟩
  · exact ⟨aliasGap27_0, aliasGap27_0_mem, aliasGap27_0_enabled 303 rfl⟩
  · exact ⟨aliasGap45_0, aliasGap45_0_mem, aliasGap45_0_enabled 303 rfl⟩
  · exact ⟨aliasGap43_0, aliasGap43_0_mem, aliasGap43_0_enabled 303 rfl⟩
  · exact ⟨aliasGap30_0, aliasGap30_0_mem, aliasGap30_0_enabled 303 rfl⟩
  · exact ⟨aliasGap31_0, aliasGap31_0_mem, aliasGap31_0_enabled 303 rfl⟩
  · exact ⟨aliasGap32_0, aliasGap32_0_mem, aliasGap32_0_enabled 303 rfl⟩
  · exact ⟨aliasGap33_0, aliasGap33_0_mem, aliasGap33_0_enabled 303 rfl⟩
  · exact ⟨aliasGap34_0, aliasGap34_0_mem, aliasGap34_0_enabled 303 rfl⟩
  · exact ⟨aliasGap35_0, aliasGap35_0_mem, aliasGap35_0_enabled 303 rfl⟩
  · exact ⟨aliasGap36_0, aliasGap36_0_mem, aliasGap36_0_enabled 303 rfl⟩
  · exact ⟨aliasGap37_0, aliasGap37_0_mem, aliasGap37_0_enabled 303 rfl⟩
  · exact ⟨aliasGap48_0, aliasGap48_0_mem, aliasGap48_0_enabled 303 rfl⟩
  · exact ⟨aliasGap49_0, aliasGap49_0_mem, aliasGap49_0_enabled 303 rfl⟩
  · exact ⟨aliasGap46_0, aliasGap46_0_mem, aliasGap46_0_enabled 303 rfl⟩
  · exact ⟨aliasGap47_0, aliasGap47_0_mem, aliasGap47_0_enabled 303 rfl⟩


end
end ElevenSquare.Tasks.T06
