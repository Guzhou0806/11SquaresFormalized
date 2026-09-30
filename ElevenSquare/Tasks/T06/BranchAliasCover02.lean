import ElevenSquare.Tasks.T06.BranchAliasDefinitions

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem raw_alias_cover_032 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 32) row), RawEnabled 32 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_033 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 33) row), RawEnabled 33 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_034 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 34) row), RawEnabled 34 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_035 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 35) row), RawEnabled 35 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_036 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 36) row), RawEnabled 36 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_037 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 37) row), RawEnabled 37 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_038 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 38) row), RawEnabled 38 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_039 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 39) row), RawEnabled 39 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_040 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 40) row), RawEnabled 40 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_041 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 41) row), RawEnabled 41 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_042 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 42) row), RawEnabled 42 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_043 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 43) row), RawEnabled 43 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_044 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 44) row), RawEnabled 44 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_045 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 45) row), RawEnabled 45 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_046 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 46) row), RawEnabled 46 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩

theorem raw_alias_cover_047 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 47) row), RawEnabled 47 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, True.intro⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self _ _, ⟨13, rfl⟩⟩


end
end ElevenSquare.Tasks.T06
