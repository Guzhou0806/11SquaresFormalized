import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts0
import ElevenSquare.Pending.S07_SelectedBanFacts1
import ElevenSquare.Pending.S07_SelectedBanFacts4
import ElevenSquare.Pending.S07_SelectedBanFacts7
import ElevenSquare.Pending.S07_SelectedBanFacts8
import ElevenSquare.Pending.S07_SelectedBanFacts9
import ElevenSquare.Pending.S07_SelectedBanFacts10
import ElevenSquare.Pending.S07_SelectedBanFacts11
import ElevenSquare.Pending.S07_SelectedBanFacts12
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good128 : NeighborGood 128 := by
  change ∀ s ∈ [4, 6, 9, 115, 180], NatPairBanned 128 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_4_128.symm, (List.forall_mem_cons.mpr ⟨used_ban_6_128.symm, (List.forall_mem_cons.mpr ⟨used_ban_9_128.symm, (List.forall_mem_cons.mpr ⟨used_ban_115_128.symm, (List.forall_mem_cons.mpr ⟨used_ban_128_180, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good129 : NeighborGood 129 := by
  change ∀ s ∈ [180], NatPairBanned 129 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_129_180, List.forall_mem_nil _⟩)
theorem neighbor_good130 : NeighborGood 130 := by
  change ∀ s ∈ [180, 189], NatPairBanned 130 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_130_180, (List.forall_mem_cons.mpr ⟨used_ban_130_189, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good131 : NeighborGood 131 := by
  change ∀ s ∈ [1, 191], NatPairBanned 131 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_1_131.symm, (List.forall_mem_cons.mpr ⟨used_ban_131_191, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good132 : NeighborGood 132 := by
  change ∀ s ∈ [], NatPairBanned 132 s
  exact List.forall_mem_nil _
theorem neighbor_good133 : NeighborGood 133 := by
  change ∀ s ∈ [187, 191, 193], NatPairBanned 133 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_133_187, (List.forall_mem_cons.mpr ⟨used_ban_133_191, (List.forall_mem_cons.mpr ⟨used_ban_133_193, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good134 : NeighborGood 134 := by
  change ∀ s ∈ [26, 65, 189], NatPairBanned 134 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_26_134.symm, (List.forall_mem_cons.mpr ⟨used_ban_65_134.symm, (List.forall_mem_cons.mpr ⟨used_ban_134_189, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good135 : NeighborGood 135 := by
  change ∀ s ∈ [187, 189, 191], NatPairBanned 135 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_135_187, (List.forall_mem_cons.mpr ⟨used_ban_135_189, (List.forall_mem_cons.mpr ⟨used_ban_135_191, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good136 : NeighborGood 136 := by
  change ∀ s ∈ [28, 40, 68, 189], NatPairBanned 136 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_28_136.symm, (List.forall_mem_cons.mpr ⟨used_ban_40_136.symm, (List.forall_mem_cons.mpr ⟨used_ban_68_136.symm, (List.forall_mem_cons.mpr ⟨used_ban_136_189, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good137 : NeighborGood 137 := by
  change ∀ s ∈ [40, 68, 187, 189, 191, 193], NatPairBanned 137 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_40_137.symm, (List.forall_mem_cons.mpr ⟨used_ban_68_137.symm, (List.forall_mem_cons.mpr ⟨used_ban_137_187, (List.forall_mem_cons.mpr ⟨used_ban_137_189, (List.forall_mem_cons.mpr ⟨used_ban_137_191, (List.forall_mem_cons.mpr ⟨used_ban_137_193, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good138 : NeighborGood 138 := by
  change ∀ s ∈ [75, 158, 166, 189], NatPairBanned 138 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_75_138.symm, (List.forall_mem_cons.mpr ⟨used_ban_138_158, (List.forall_mem_cons.mpr ⟨used_ban_138_166, (List.forall_mem_cons.mpr ⟨used_ban_138_189, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good139 : NeighborGood 139 := by
  change ∀ s ∈ [40, 68, 69, 187, 189, 191], NatPairBanned 139 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_40_139.symm, (List.forall_mem_cons.mpr ⟨used_ban_68_139.symm, (List.forall_mem_cons.mpr ⟨used_ban_69_139.symm, (List.forall_mem_cons.mpr ⟨used_ban_139_187, (List.forall_mem_cons.mpr ⟨used_ban_139_189, (List.forall_mem_cons.mpr ⟨used_ban_139_191, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good140 : NeighborGood 140 := by
  change ∀ s ∈ [115], NatPairBanned 140 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_115_140.symm, List.forall_mem_nil _⟩)
theorem neighbor_good141 : NeighborGood 141 := by
  change ∀ s ∈ [], NatPairBanned 141 s
  exact List.forall_mem_nil _
theorem neighbor_good142 : NeighborGood 142 := by
  change ∀ s ∈ [114, 118, 121, 199], NatPairBanned 142 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_114_142.symm, (List.forall_mem_cons.mpr ⟨used_ban_118_142.symm, (List.forall_mem_cons.mpr ⟨used_ban_121_142.symm, (List.forall_mem_cons.mpr ⟨used_ban_142_199, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good143 : NeighborGood 143 := by
  change ∀ s ∈ [86, 121, 180], NatPairBanned 143 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_86_143.symm, (List.forall_mem_cons.mpr ⟨used_ban_121_143.symm, (List.forall_mem_cons.mpr ⟨used_ban_143_180, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbors_range8 : AllRange NeighborGood 128 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good128, (List.forall_mem_cons.mpr ⟨neighbor_good129, (List.forall_mem_cons.mpr ⟨neighbor_good130, (List.forall_mem_cons.mpr ⟨neighbor_good131, (List.forall_mem_cons.mpr ⟨neighbor_good132, (List.forall_mem_cons.mpr ⟨neighbor_good133, (List.forall_mem_cons.mpr ⟨neighbor_good134, (List.forall_mem_cons.mpr ⟨neighbor_good135, (List.forall_mem_cons.mpr ⟨neighbor_good136, (List.forall_mem_cons.mpr ⟨neighbor_good137, (List.forall_mem_cons.mpr ⟨neighbor_good138, (List.forall_mem_cons.mpr ⟨neighbor_good139, (List.forall_mem_cons.mpr ⟨neighbor_good140, (List.forall_mem_cons.mpr ⟨neighbor_good141, (List.forall_mem_cons.mpr ⟨neighbor_good142, (List.forall_mem_cons.mpr ⟨neighbor_good143, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range8
