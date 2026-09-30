import ElevenSquare.Tasks.T06.BranchAliasDefinitions

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem raw_alias_cover_016 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 16) row), RawEnabled 16 g := by
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

theorem raw_alias_cover_017 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 17) row), RawEnabled 17 g := by
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

theorem raw_alias_cover_018 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 18) row), RawEnabled 18 g := by
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

theorem raw_alias_cover_019 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 19) row), RawEnabled 19 g := by
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

theorem raw_alias_cover_020 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 20) row), RawEnabled 20 g := by
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

theorem raw_alias_cover_021 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 21) row), RawEnabled 21 g := by
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

theorem raw_alias_cover_022 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 22) row), RawEnabled 22 g := by
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

theorem raw_alias_cover_023 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 23) row), RawEnabled 23 g := by
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

theorem raw_alias_cover_024 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 24) row), RawEnabled 24 g := by
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

theorem raw_alias_cover_025 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 25) row), RawEnabled 25 g := by
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

theorem raw_alias_cover_026 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 26) row), RawEnabled 26 g := by
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

theorem raw_alias_cover_027 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 27) row), RawEnabled 27 g := by
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

theorem raw_alias_cover_028 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 28) row), RawEnabled 28 g := by
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

theorem raw_alias_cover_029 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 29) row), RawEnabled 29 g := by
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

theorem raw_alias_cover_030 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 30) row), RawEnabled 30 g := by
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

theorem raw_alias_cover_031 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 31) row), RawEnabled 31 g := by
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
