import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts7
import ElevenSquare.Pending.S07_SelectedBanFacts9
import ElevenSquare.Pending.S07_SelectedBanFacts10
import ElevenSquare.Pending.S07_SelectedBanFacts11
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good112 : NeighborGood 112 := by
  change ∀ s ∈ [182, 183, 185], NatPairBanned 112 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_112_182, (List.forall_mem_cons.mpr ⟨used_ban_112_183, (List.forall_mem_cons.mpr ⟨used_ban_112_185, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good113 : NeighborGood 113 := by
  change ∀ s ∈ [184], NatPairBanned 113 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_113_184, List.forall_mem_nil _⟩)
theorem neighbor_good114 : NeighborGood 114 := by
  change ∀ s ∈ [142, 181, 183], NatPairBanned 114 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_114_142, (List.forall_mem_cons.mpr ⟨used_ban_114_181, (List.forall_mem_cons.mpr ⟨used_ban_114_183, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good115 : NeighborGood 115 := by
  change ∀ s ∈ [40, 41, 43, 45, 127, 128, 140, 180, 181, 190], NatPairBanned 115 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_40_115.symm, (List.forall_mem_cons.mpr ⟨used_ban_41_115.symm, (List.forall_mem_cons.mpr ⟨used_ban_43_115.symm, (List.forall_mem_cons.mpr ⟨used_ban_45_115.symm, (List.forall_mem_cons.mpr ⟨used_ban_115_127, (List.forall_mem_cons.mpr ⟨used_ban_115_128, (List.forall_mem_cons.mpr ⟨used_ban_115_140, (List.forall_mem_cons.mpr ⟨used_ban_115_180, (List.forall_mem_cons.mpr ⟨used_ban_115_181, (List.forall_mem_cons.mpr ⟨used_ban_115_190, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good116 : NeighborGood 116 := by
  change ∀ s ∈ [41, 180, 181], NatPairBanned 116 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_41_116.symm, (List.forall_mem_cons.mpr ⟨used_ban_116_180, (List.forall_mem_cons.mpr ⟨used_ban_116_181, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good117 : NeighborGood 117 := by
  change ∀ s ∈ [180, 181, 185, 186, 190, 198], NatPairBanned 117 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_117_180, (List.forall_mem_cons.mpr ⟨used_ban_117_181, (List.forall_mem_cons.mpr ⟨used_ban_117_185, (List.forall_mem_cons.mpr ⟨used_ban_117_186, (List.forall_mem_cons.mpr ⟨used_ban_117_190, (List.forall_mem_cons.mpr ⟨used_ban_117_198, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good118 : NeighborGood 118 := by
  change ∀ s ∈ [42, 127, 142, 180], NatPairBanned 118 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_42_118.symm, (List.forall_mem_cons.mpr ⟨used_ban_118_127, (List.forall_mem_cons.mpr ⟨used_ban_118_142, (List.forall_mem_cons.mpr ⟨used_ban_118_180, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good119 : NeighborGood 119 := by
  change ∀ s ∈ [181, 183], NatPairBanned 119 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_119_181, (List.forall_mem_cons.mpr ⟨used_ban_119_183, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good120 : NeighborGood 120 := by
  change ∀ s ∈ [181, 183, 190], NatPairBanned 120 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_120_181, (List.forall_mem_cons.mpr ⟨used_ban_120_183, (List.forall_mem_cons.mpr ⟨used_ban_120_190, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good121 : NeighborGood 121 := by
  change ∀ s ∈ [142, 143], NatPairBanned 121 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_121_142, (List.forall_mem_cons.mpr ⟨used_ban_121_143, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good122 : NeighborGood 122 := by
  change ∀ s ∈ [180, 181, 186], NatPairBanned 122 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_122_180, (List.forall_mem_cons.mpr ⟨used_ban_122_181, (List.forall_mem_cons.mpr ⟨used_ban_122_186, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good123 : NeighborGood 123 := by
  change ∀ s ∈ [180, 181, 186, 190], NatPairBanned 123 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_123_180, (List.forall_mem_cons.mpr ⟨used_ban_123_181, (List.forall_mem_cons.mpr ⟨used_ban_123_186, (List.forall_mem_cons.mpr ⟨used_ban_123_190, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good124 : NeighborGood 124 := by
  change ∀ s ∈ [180, 182, 183, 195], NatPairBanned 124 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_124_180, (List.forall_mem_cons.mpr ⟨used_ban_124_182, (List.forall_mem_cons.mpr ⟨used_ban_124_183, (List.forall_mem_cons.mpr ⟨used_ban_124_195, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good125 : NeighborGood 125 := by
  change ∀ s ∈ [180, 182, 183, 194, 197], NatPairBanned 125 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_125_180, (List.forall_mem_cons.mpr ⟨used_ban_125_182, (List.forall_mem_cons.mpr ⟨used_ban_125_183, (List.forall_mem_cons.mpr ⟨used_ban_125_194, (List.forall_mem_cons.mpr ⟨used_ban_125_197, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good126 : NeighborGood 126 := by
  change ∀ s ∈ [], NatPairBanned 126 s
  exact List.forall_mem_nil _
theorem neighbor_good127 : NeighborGood 127 := by
  change ∀ s ∈ [47, 111, 115, 118, 180, 181, 191], NatPairBanned 127 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_47_127.symm, (List.forall_mem_cons.mpr ⟨used_ban_111_127.symm, (List.forall_mem_cons.mpr ⟨used_ban_115_127.symm, (List.forall_mem_cons.mpr ⟨used_ban_118_127.symm, (List.forall_mem_cons.mpr ⟨used_ban_127_180, (List.forall_mem_cons.mpr ⟨used_ban_127_181, (List.forall_mem_cons.mpr ⟨used_ban_127_191, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbors_range7 : AllRange NeighborGood 112 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good112, (List.forall_mem_cons.mpr ⟨neighbor_good113, (List.forall_mem_cons.mpr ⟨neighbor_good114, (List.forall_mem_cons.mpr ⟨neighbor_good115, (List.forall_mem_cons.mpr ⟨neighbor_good116, (List.forall_mem_cons.mpr ⟨neighbor_good117, (List.forall_mem_cons.mpr ⟨neighbor_good118, (List.forall_mem_cons.mpr ⟨neighbor_good119, (List.forall_mem_cons.mpr ⟨neighbor_good120, (List.forall_mem_cons.mpr ⟨neighbor_good121, (List.forall_mem_cons.mpr ⟨neighbor_good122, (List.forall_mem_cons.mpr ⟨neighbor_good123, (List.forall_mem_cons.mpr ⟨neighbor_good124, (List.forall_mem_cons.mpr ⟨neighbor_good125, (List.forall_mem_cons.mpr ⟨neighbor_good126, (List.forall_mem_cons.mpr ⟨neighbor_good127, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range7
