import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts6
import ElevenSquare.Pending.S07_SelectedBanFacts7
import ElevenSquare.Pending.S07_SelectedBanFacts9
import ElevenSquare.Pending.S07_SelectedBanFacts11
import ElevenSquare.Pending.S07_SelectedBanFacts13
import ElevenSquare.Pending.S07_SelectedBanFacts14
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good160 : NeighborGood 160 := by
  change ∀ s ∈ [193], NatPairBanned 160 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_160_193, List.forall_mem_nil _⟩)
theorem neighbor_good161 : NeighborGood 161 := by
  change ∀ s ∈ [189, 193], NatPairBanned 161 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_161_189, (List.forall_mem_cons.mpr ⟨used_ban_161_193, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good162 : NeighborGood 162 := by
  change ∀ s ∈ [111, 180, 181, 189, 200, 205, 206], NatPairBanned 162 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_111_162.symm, (List.forall_mem_cons.mpr ⟨used_ban_162_180, (List.forall_mem_cons.mpr ⟨used_ban_162_181, (List.forall_mem_cons.mpr ⟨used_ban_162_189, (List.forall_mem_cons.mpr ⟨used_ban_162_200, (List.forall_mem_cons.mpr ⟨used_ban_162_205, (List.forall_mem_cons.mpr ⟨used_ban_162_206, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good163 : NeighborGood 163 := by
  change ∀ s ∈ [189, 200], NatPairBanned 163 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_163_189, (List.forall_mem_cons.mpr ⟨used_ban_163_200, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good164 : NeighborGood 164 := by
  change ∀ s ∈ [187, 205], NatPairBanned 164 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_164_187, (List.forall_mem_cons.mpr ⟨used_ban_164_205, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good165 : NeighborGood 165 := by
  change ∀ s ∈ [189, 193, 200, 201, 216], NatPairBanned 165 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_165_189, (List.forall_mem_cons.mpr ⟨used_ban_165_193, (List.forall_mem_cons.mpr ⟨used_ban_165_200, (List.forall_mem_cons.mpr ⟨used_ban_165_201, (List.forall_mem_cons.mpr ⟨used_ban_165_216, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good166 : NeighborGood 166 := by
  change ∀ s ∈ [39, 138, 218], NatPairBanned 166 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_39_166.symm, (List.forall_mem_cons.mpr ⟨used_ban_138_166.symm, (List.forall_mem_cons.mpr ⟨used_ban_166_218, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good167 : NeighborGood 167 := by
  change ∀ s ∈ [39], NatPairBanned 167 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_39_167.symm, List.forall_mem_nil _⟩)
theorem neighbor_good168 : NeighborGood 168 := by
  change ∀ s ∈ [38, 39, 108, 218], NatPairBanned 168 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_38_168.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_168.symm, (List.forall_mem_cons.mpr ⟨used_ban_108_168.symm, (List.forall_mem_cons.mpr ⟨used_ban_168_218, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good169 : NeighborGood 169 := by
  change ∀ s ∈ [38, 39], NatPairBanned 169 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_38_169.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_169.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good170 : NeighborGood 170 := by
  change ∀ s ∈ [], NatPairBanned 170 s
  exact List.forall_mem_nil _
theorem neighbor_good171 : NeighborGood 171 := by
  change ∀ s ∈ [38, 39, 92], NatPairBanned 171 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_38_171.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_171.symm, (List.forall_mem_cons.mpr ⟨used_ban_92_171.symm, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good172 : NeighborGood 172 := by
  change ∀ s ∈ [92], NatPairBanned 172 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_92_172.symm, List.forall_mem_nil _⟩)
theorem neighbor_good173 : NeighborGood 173 := by
  change ∀ s ∈ [218], NatPairBanned 173 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_173_218, List.forall_mem_nil _⟩)
theorem neighbor_good174 : NeighborGood 174 := by
  change ∀ s ∈ [104], NatPairBanned 174 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_104_174.symm, List.forall_mem_nil _⟩)
theorem neighbor_good175 : NeighborGood 175 := by
  change ∀ s ∈ [], NatPairBanned 175 s
  exact List.forall_mem_nil _
theorem neighbors_range10 : AllRange NeighborGood 160 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good160, (List.forall_mem_cons.mpr ⟨neighbor_good161, (List.forall_mem_cons.mpr ⟨neighbor_good162, (List.forall_mem_cons.mpr ⟨neighbor_good163, (List.forall_mem_cons.mpr ⟨neighbor_good164, (List.forall_mem_cons.mpr ⟨neighbor_good165, (List.forall_mem_cons.mpr ⟨neighbor_good166, (List.forall_mem_cons.mpr ⟨neighbor_good167, (List.forall_mem_cons.mpr ⟨neighbor_good168, (List.forall_mem_cons.mpr ⟨neighbor_good169, (List.forall_mem_cons.mpr ⟨neighbor_good170, (List.forall_mem_cons.mpr ⟨neighbor_good171, (List.forall_mem_cons.mpr ⟨neighbor_good172, (List.forall_mem_cons.mpr ⟨neighbor_good173, (List.forall_mem_cons.mpr ⟨neighbor_good174, (List.forall_mem_cons.mpr ⟨neighbor_good175, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range10
