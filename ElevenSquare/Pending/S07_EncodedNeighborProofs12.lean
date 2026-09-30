import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts8
import ElevenSquare.Pending.S07_SelectedBanFacts10
import ElevenSquare.Pending.S07_SelectedBanFacts11
import ElevenSquare.Pending.S07_SelectedBanFacts12
import ElevenSquare.Pending.S07_SelectedBanFacts13
import ElevenSquare.Pending.S07_SelectedBanFacts14
import ElevenSquare.Pending.S07_SelectedBanFacts15
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good192 : NeighborGood 192 := by
  change ∀ s ∈ [], NatPairBanned 192 s
  exact List.forall_mem_nil _
theorem neighbor_good193 : NeighborGood 193 := by
  change ∀ s ∈ [85, 133, 137, 145, 146, 147, 148, 151, 156, 157, 158, 159, 160, 161, 165, 183, 202, 205, 206, 208, 209, 210, 218, 219], NatPairBanned 193 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_85_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_133_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_137_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_145_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_146_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_147_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_148_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_151_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_156_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_157_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_158_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_159_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_160_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_161_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_165_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_183_193.symm, (List.forall_mem_cons.mpr ⟨used_ban_193_202, (List.forall_mem_cons.mpr ⟨used_ban_193_205, (List.forall_mem_cons.mpr ⟨used_ban_193_206, (List.forall_mem_cons.mpr ⟨used_ban_193_208, (List.forall_mem_cons.mpr ⟨used_ban_193_209, (List.forall_mem_cons.mpr ⟨used_ban_193_210, (List.forall_mem_cons.mpr ⟨used_ban_193_218, (List.forall_mem_cons.mpr ⟨used_ban_193_219, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good194 : NeighborGood 194 := by
  change ∀ s ∈ [125, 145, 146, 147, 154, 156, 157, 180, 181, 208, 209, 210], NatPairBanned 194 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_125_194.symm, (List.forall_mem_cons.mpr ⟨used_ban_145_194.symm, (List.forall_mem_cons.mpr ⟨used_ban_146_194.symm, (List.forall_mem_cons.mpr ⟨used_ban_147_194.symm, (List.forall_mem_cons.mpr ⟨used_ban_154_194.symm, (List.forall_mem_cons.mpr ⟨used_ban_156_194.symm, (List.forall_mem_cons.mpr ⟨used_ban_157_194.symm, (List.forall_mem_cons.mpr ⟨used_ban_180_194.symm, (List.forall_mem_cons.mpr ⟨used_ban_181_194.symm, (List.forall_mem_cons.mpr ⟨used_ban_194_208, (List.forall_mem_cons.mpr ⟨used_ban_194_209, (List.forall_mem_cons.mpr ⟨used_ban_194_210, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good195 : NeighborGood 195 := by
  change ∀ s ∈ [124, 202], NatPairBanned 195 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_124_195.symm, (List.forall_mem_cons.mpr ⟨used_ban_195_202, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good196 : NeighborGood 196 := by
  change ∀ s ∈ [], NatPairBanned 196 s
  exact List.forall_mem_nil _
theorem neighbor_good197 : NeighborGood 197 := by
  change ∀ s ∈ [125, 180, 181, 185, 204], NatPairBanned 197 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_125_197.symm, (List.forall_mem_cons.mpr ⟨used_ban_180_197.symm, (List.forall_mem_cons.mpr ⟨used_ban_181_197.symm, (List.forall_mem_cons.mpr ⟨used_ban_185_197.symm, (List.forall_mem_cons.mpr ⟨used_ban_197_204, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good198 : NeighborGood 198 := by
  change ∀ s ∈ [117], NatPairBanned 198 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_117_198.symm, List.forall_mem_nil _⟩)
theorem neighbor_good199 : NeighborGood 199 := by
  change ∀ s ∈ [142], NatPairBanned 199 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_142_199.symm, List.forall_mem_nil _⟩)
theorem neighbor_good200 : NeighborGood 200 := by
  change ∀ s ∈ [147, 152, 162, 163, 165, 210, 212, 213, 215], NatPairBanned 200 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_147_200.symm, (List.forall_mem_cons.mpr ⟨used_ban_152_200.symm, (List.forall_mem_cons.mpr ⟨used_ban_162_200.symm, (List.forall_mem_cons.mpr ⟨used_ban_163_200.symm, (List.forall_mem_cons.mpr ⟨used_ban_165_200.symm, (List.forall_mem_cons.mpr ⟨used_ban_200_210, (List.forall_mem_cons.mpr ⟨used_ban_200_212, (List.forall_mem_cons.mpr ⟨used_ban_200_213, (List.forall_mem_cons.mpr ⟨used_ban_200_215, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good201 : NeighborGood 201 := by
  change ∀ s ∈ [147, 165, 210, 213], NatPairBanned 201 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_147_201.symm, (List.forall_mem_cons.mpr ⟨used_ban_165_201.symm, (List.forall_mem_cons.mpr ⟨used_ban_201_210, (List.forall_mem_cons.mpr ⟨used_ban_201_213, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good202 : NeighborGood 202 := by
  change ∀ s ∈ [145, 146, 147, 156, 157, 193, 195, 208, 209, 210, 216], NatPairBanned 202 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_145_202.symm, (List.forall_mem_cons.mpr ⟨used_ban_146_202.symm, (List.forall_mem_cons.mpr ⟨used_ban_147_202.symm, (List.forall_mem_cons.mpr ⟨used_ban_156_202.symm, (List.forall_mem_cons.mpr ⟨used_ban_157_202.symm, (List.forall_mem_cons.mpr ⟨used_ban_193_202.symm, (List.forall_mem_cons.mpr ⟨used_ban_195_202.symm, (List.forall_mem_cons.mpr ⟨used_ban_202_208, (List.forall_mem_cons.mpr ⟨used_ban_202_209, (List.forall_mem_cons.mpr ⟨used_ban_202_210, (List.forall_mem_cons.mpr ⟨used_ban_202_216, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good203 : NeighborGood 203 := by
  change ∀ s ∈ [147, 152, 210], NatPairBanned 203 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_147_203.symm, (List.forall_mem_cons.mpr ⟨used_ban_152_203.symm, (List.forall_mem_cons.mpr ⟨used_ban_203_210, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good204 : NeighborGood 204 := by
  change ∀ s ∈ [147, 148, 152, 153, 155, 189, 197, 210, 213], NatPairBanned 204 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_147_204.symm, (List.forall_mem_cons.mpr ⟨used_ban_148_204.symm, (List.forall_mem_cons.mpr ⟨used_ban_152_204.symm, (List.forall_mem_cons.mpr ⟨used_ban_153_204.symm, (List.forall_mem_cons.mpr ⟨used_ban_155_204.symm, (List.forall_mem_cons.mpr ⟨used_ban_189_204.symm, (List.forall_mem_cons.mpr ⟨used_ban_197_204.symm, (List.forall_mem_cons.mpr ⟨used_ban_204_210, (List.forall_mem_cons.mpr ⟨used_ban_204_213, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good205 : NeighborGood 205 := by
  change ∀ s ∈ [155, 162, 164, 193, 218], NatPairBanned 205 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_155_205.symm, (List.forall_mem_cons.mpr ⟨used_ban_162_205.symm, (List.forall_mem_cons.mpr ⟨used_ban_164_205.symm, (List.forall_mem_cons.mpr ⟨used_ban_193_205.symm, (List.forall_mem_cons.mpr ⟨used_ban_205_218, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good206 : NeighborGood 206 := by
  change ∀ s ∈ [162, 193], NatPairBanned 206 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_162_206.symm, (List.forall_mem_cons.mpr ⟨used_ban_193_206.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good207 : NeighborGood 207 := by
  change ∀ s ∈ [], NatPairBanned 207 s
  exact List.forall_mem_nil _
theorem neighbors_range12 : AllRange NeighborGood 192 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good192, (List.forall_mem_cons.mpr ⟨neighbor_good193, (List.forall_mem_cons.mpr ⟨neighbor_good194, (List.forall_mem_cons.mpr ⟨neighbor_good195, (List.forall_mem_cons.mpr ⟨neighbor_good196, (List.forall_mem_cons.mpr ⟨neighbor_good197, (List.forall_mem_cons.mpr ⟨neighbor_good198, (List.forall_mem_cons.mpr ⟨neighbor_good199, (List.forall_mem_cons.mpr ⟨neighbor_good200, (List.forall_mem_cons.mpr ⟨neighbor_good201, (List.forall_mem_cons.mpr ⟨neighbor_good202, (List.forall_mem_cons.mpr ⟨neighbor_good203, (List.forall_mem_cons.mpr ⟨neighbor_good204, (List.forall_mem_cons.mpr ⟨neighbor_good205, (List.forall_mem_cons.mpr ⟨neighbor_good206, (List.forall_mem_cons.mpr ⟨neighbor_good207, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range12
