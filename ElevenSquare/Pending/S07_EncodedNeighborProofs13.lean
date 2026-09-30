import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts8
import ElevenSquare.Pending.S07_SelectedBanFacts9
import ElevenSquare.Pending.S07_SelectedBanFacts12
import ElevenSquare.Pending.S07_SelectedBanFacts13
import ElevenSquare.Pending.S07_SelectedBanFacts14
import ElevenSquare.Pending.S07_SelectedBanFacts15
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good208 : NeighborGood 208 := by
  change ∀ s ∈ [189, 193, 194, 202], NatPairBanned 208 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_189_208.symm, (List.forall_mem_cons.mpr ⟨used_ban_193_208.symm, (List.forall_mem_cons.mpr ⟨used_ban_194_208.symm, (List.forall_mem_cons.mpr ⟨used_ban_202_208.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good209 : NeighborGood 209 := by
  change ∀ s ∈ [88, 92, 189, 193, 194, 202], NatPairBanned 209 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_88_209.symm, (List.forall_mem_cons.mpr ⟨used_ban_92_209.symm, (List.forall_mem_cons.mpr ⟨used_ban_189_209.symm, (List.forall_mem_cons.mpr ⟨used_ban_193_209.symm, (List.forall_mem_cons.mpr ⟨used_ban_194_209.symm, (List.forall_mem_cons.mpr ⟨used_ban_202_209.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good210 : NeighborGood 210 := by
  change ∀ s ∈ [189, 193, 194, 200, 201, 202, 203, 204], NatPairBanned 210 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_189_210.symm, (List.forall_mem_cons.mpr ⟨used_ban_193_210.symm, (List.forall_mem_cons.mpr ⟨used_ban_194_210.symm, (List.forall_mem_cons.mpr ⟨used_ban_200_210.symm, (List.forall_mem_cons.mpr ⟨used_ban_201_210.symm, (List.forall_mem_cons.mpr ⟨used_ban_202_210.symm, (List.forall_mem_cons.mpr ⟨used_ban_203_210.symm, (List.forall_mem_cons.mpr ⟨used_ban_204_210.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good211 : NeighborGood 211 := by
  change ∀ s ∈ [], NatPairBanned 211 s
  exact List.forall_mem_nil _
theorem neighbor_good212 : NeighborGood 212 := by
  change ∀ s ∈ [200], NatPairBanned 212 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_200_212.symm, List.forall_mem_nil _⟩)
theorem neighbor_good213 : NeighborGood 213 := by
  change ∀ s ∈ [200, 201, 204], NatPairBanned 213 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_200_213.symm, (List.forall_mem_cons.mpr ⟨used_ban_201_213.symm, (List.forall_mem_cons.mpr ⟨used_ban_204_213.symm, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good214 : NeighborGood 214 := by
  change ∀ s ∈ [], NatPairBanned 214 s
  exact List.forall_mem_nil _
theorem neighbor_good215 : NeighborGood 215 := by
  change ∀ s ∈ [200], NatPairBanned 215 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_200_215.symm, List.forall_mem_nil _⟩)
theorem neighbor_good216 : NeighborGood 216 := by
  change ∀ s ∈ [165, 202], NatPairBanned 216 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_165_216.symm, (List.forall_mem_cons.mpr ⟨used_ban_202_216.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good217 : NeighborGood 217 := by
  change ∀ s ∈ [], NatPairBanned 217 s
  exact List.forall_mem_nil _
theorem neighbor_good218 : NeighborGood 218 := by
  change ∀ s ∈ [75, 88, 92, 149, 150, 151, 152, 154, 166, 168, 173, 178, 179, 193, 205], NatPairBanned 218 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_75_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_88_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_92_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_149_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_150_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_151_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_152_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_154_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_166_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_168_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_173_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_178_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_179_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_193_218.symm, (List.forall_mem_cons.mpr ⟨used_ban_205_218.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good219 : NeighborGood 219 := by
  change ∀ s ∈ [151, 152, 153, 155, 189, 193], NatPairBanned 219 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_151_219.symm, (List.forall_mem_cons.mpr ⟨used_ban_152_219.symm, (List.forall_mem_cons.mpr ⟨used_ban_153_219.symm, (List.forall_mem_cons.mpr ⟨used_ban_155_219.symm, (List.forall_mem_cons.mpr ⟨used_ban_189_219.symm, (List.forall_mem_cons.mpr ⟨used_ban_193_219.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbors_range13 : AllRange NeighborGood 208 12 := by
  apply AllRange.of_list
  change ∀ r ∈ [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good208, (List.forall_mem_cons.mpr ⟨neighbor_good209, (List.forall_mem_cons.mpr ⟨neighbor_good210, (List.forall_mem_cons.mpr ⟨neighbor_good211, (List.forall_mem_cons.mpr ⟨neighbor_good212, (List.forall_mem_cons.mpr ⟨neighbor_good213, (List.forall_mem_cons.mpr ⟨neighbor_good214, (List.forall_mem_cons.mpr ⟨neighbor_good215, (List.forall_mem_cons.mpr ⟨neighbor_good216, (List.forall_mem_cons.mpr ⟨neighbor_good217, (List.forall_mem_cons.mpr ⟨neighbor_good218, (List.forall_mem_cons.mpr ⟨neighbor_good219, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range13
