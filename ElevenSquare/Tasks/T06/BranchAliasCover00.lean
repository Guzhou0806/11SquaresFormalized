import ElevenSquare.Tasks.T06.BranchAliasDefinitions

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem raw_alias_cover_000 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 0) row), RawEnabled 0 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_001 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 1) row), RawEnabled 1 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_002 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 2) row), RawEnabled 2 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_003 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 3) row), RawEnabled 3 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_004 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 4) row), RawEnabled 4 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_005 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 5) row), RawEnabled 5 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_006 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 6) row), RawEnabled 6 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_007 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 7) row), RawEnabled 7 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_008 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 8) row), RawEnabled 8 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_009 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 9) row), RawEnabled 9 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_010 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 10) row), RawEnabled 10 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_011 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 11) row), RawEnabled 11 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_012 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 12) row), RawEnabled 12 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_013 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 13) row), RawEnabled 13 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_014 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 14) row), RawEnabled 14 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩

theorem raw_alias_cover_015 (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch 15) row), RawEnabled 15 g := by
  fin_cases row
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, True.intro⟩
  · exact ⟨_, List.mem_cons_self, ⟨0, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨1, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨2, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨3, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨4, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨5, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨6, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨7, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨8, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨9, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨10, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨11, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨12, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩
  · exact ⟨_, List.mem_cons_self, ⟨13, rfl⟩⟩


end
end ElevenSquare.Tasks.T06
