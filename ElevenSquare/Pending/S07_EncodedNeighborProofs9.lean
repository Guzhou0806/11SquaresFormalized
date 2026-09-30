import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts0
import ElevenSquare.Pending.S07_SelectedBanFacts8
import ElevenSquare.Pending.S07_SelectedBanFacts9
import ElevenSquare.Pending.S07_SelectedBanFacts11
import ElevenSquare.Pending.S07_SelectedBanFacts12
import ElevenSquare.Pending.S07_SelectedBanFacts13
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good144 : NeighborGood 144 := by
  change ∀ s ∈ [4, 5, 70, 180], NatPairBanned 144 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_4_144.symm, (List.forall_mem_cons.mpr ⟨used_ban_5_144.symm, (List.forall_mem_cons.mpr ⟨used_ban_70_144.symm, (List.forall_mem_cons.mpr ⟨used_ban_144_180, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good145 : NeighborGood 145 := by
  change ∀ s ∈ [189, 193, 194, 202], NatPairBanned 145 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_145_189, (List.forall_mem_cons.mpr ⟨used_ban_145_193, (List.forall_mem_cons.mpr ⟨used_ban_145_194, (List.forall_mem_cons.mpr ⟨used_ban_145_202, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good146 : NeighborGood 146 := by
  change ∀ s ∈ [189, 193, 194, 202], NatPairBanned 146 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_146_189, (List.forall_mem_cons.mpr ⟨used_ban_146_193, (List.forall_mem_cons.mpr ⟨used_ban_146_194, (List.forall_mem_cons.mpr ⟨used_ban_146_202, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good147 : NeighborGood 147 := by
  change ∀ s ∈ [189, 193, 194, 200, 201, 202, 203, 204], NatPairBanned 147 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_147_189, (List.forall_mem_cons.mpr ⟨used_ban_147_193, (List.forall_mem_cons.mpr ⟨used_ban_147_194, (List.forall_mem_cons.mpr ⟨used_ban_147_200, (List.forall_mem_cons.mpr ⟨used_ban_147_201, (List.forall_mem_cons.mpr ⟨used_ban_147_202, (List.forall_mem_cons.mpr ⟨used_ban_147_203, (List.forall_mem_cons.mpr ⟨used_ban_147_204, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good148 : NeighborGood 148 := by
  change ∀ s ∈ [189, 193, 204], NatPairBanned 148 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_148_189, (List.forall_mem_cons.mpr ⟨used_ban_148_193, (List.forall_mem_cons.mpr ⟨used_ban_148_204, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good149 : NeighborGood 149 := by
  change ∀ s ∈ [189, 218], NatPairBanned 149 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_149_189, (List.forall_mem_cons.mpr ⟨used_ban_149_218, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good150 : NeighborGood 150 := by
  change ∀ s ∈ [218], NatPairBanned 150 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_150_218, List.forall_mem_nil _⟩)
theorem neighbor_good151 : NeighborGood 151 := by
  change ∀ s ∈ [193, 218, 219], NatPairBanned 151 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_151_193, (List.forall_mem_cons.mpr ⟨used_ban_151_218, (List.forall_mem_cons.mpr ⟨used_ban_151_219, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good152 : NeighborGood 152 := by
  change ∀ s ∈ [200, 203, 204, 218, 219], NatPairBanned 152 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_152_200, (List.forall_mem_cons.mpr ⟨used_ban_152_203, (List.forall_mem_cons.mpr ⟨used_ban_152_204, (List.forall_mem_cons.mpr ⟨used_ban_152_218, (List.forall_mem_cons.mpr ⟨used_ban_152_219, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good153 : NeighborGood 153 := by
  change ∀ s ∈ [204, 219], NatPairBanned 153 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_153_204, (List.forall_mem_cons.mpr ⟨used_ban_153_219, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good154 : NeighborGood 154 := by
  change ∀ s ∈ [194, 218], NatPairBanned 154 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_154_194, (List.forall_mem_cons.mpr ⟨used_ban_154_218, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good155 : NeighborGood 155 := by
  change ∀ s ∈ [183, 204, 205, 219], NatPairBanned 155 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_155_183, (List.forall_mem_cons.mpr ⟨used_ban_155_204, (List.forall_mem_cons.mpr ⟨used_ban_155_205, (List.forall_mem_cons.mpr ⟨used_ban_155_219, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good156 : NeighborGood 156 := by
  change ∀ s ∈ [189, 193, 194, 202], NatPairBanned 156 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_156_189, (List.forall_mem_cons.mpr ⟨used_ban_156_193, (List.forall_mem_cons.mpr ⟨used_ban_156_194, (List.forall_mem_cons.mpr ⟨used_ban_156_202, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good157 : NeighborGood 157 := by
  change ∀ s ∈ [189, 193, 194, 202], NatPairBanned 157 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_157_189, (List.forall_mem_cons.mpr ⟨used_ban_157_193, (List.forall_mem_cons.mpr ⟨used_ban_157_194, (List.forall_mem_cons.mpr ⟨used_ban_157_202, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good158 : NeighborGood 158 := by
  change ∀ s ∈ [111, 138, 180, 181, 191, 193], NatPairBanned 158 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_111_158.symm, (List.forall_mem_cons.mpr ⟨used_ban_138_158.symm, (List.forall_mem_cons.mpr ⟨used_ban_158_180, (List.forall_mem_cons.mpr ⟨used_ban_158_181, (List.forall_mem_cons.mpr ⟨used_ban_158_191, (List.forall_mem_cons.mpr ⟨used_ban_158_193, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good159 : NeighborGood 159 := by
  change ∀ s ∈ [189, 193], NatPairBanned 159 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_159_189, (List.forall_mem_cons.mpr ⟨used_ban_159_193, List.forall_mem_nil _⟩)⟩)
theorem neighbors_range9 : AllRange NeighborGood 144 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good144, (List.forall_mem_cons.mpr ⟨neighbor_good145, (List.forall_mem_cons.mpr ⟨neighbor_good146, (List.forall_mem_cons.mpr ⟨neighbor_good147, (List.forall_mem_cons.mpr ⟨neighbor_good148, (List.forall_mem_cons.mpr ⟨neighbor_good149, (List.forall_mem_cons.mpr ⟨neighbor_good150, (List.forall_mem_cons.mpr ⟨neighbor_good151, (List.forall_mem_cons.mpr ⟨neighbor_good152, (List.forall_mem_cons.mpr ⟨neighbor_good153, (List.forall_mem_cons.mpr ⟨neighbor_good154, (List.forall_mem_cons.mpr ⟨neighbor_good155, (List.forall_mem_cons.mpr ⟨neighbor_good156, (List.forall_mem_cons.mpr ⟨neighbor_good157, (List.forall_mem_cons.mpr ⟨neighbor_good158, (List.forall_mem_cons.mpr ⟨neighbor_good159, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range9
