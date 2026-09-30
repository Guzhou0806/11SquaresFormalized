import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts7
import ElevenSquare.Pending.S07_SelectedBanFacts8
import ElevenSquare.Pending.S07_SelectedBanFacts9
import ElevenSquare.Pending.S07_SelectedBanFacts10
import ElevenSquare.Pending.S07_SelectedBanFacts11
import ElevenSquare.Pending.S07_SelectedBanFacts12
import ElevenSquare.Pending.S07_SelectedBanFacts13
import ElevenSquare.Pending.S07_SelectedBanFacts14
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good176 : NeighborGood 176 := by
  change ∀ s ∈ [88, 104], NatPairBanned 176 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_88_176.symm, (List.forall_mem_cons.mpr ⟨used_ban_104_176.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good177 : NeighborGood 177 := by
  change ∀ s ∈ [92, 101], NatPairBanned 177 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_92_177.symm, (List.forall_mem_cons.mpr ⟨used_ban_101_177.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good178 : NeighborGood 178 := by
  change ∀ s ∈ [39, 103, 104, 218], NatPairBanned 178 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_39_178.symm, (List.forall_mem_cons.mpr ⟨used_ban_103_178.symm, (List.forall_mem_cons.mpr ⟨used_ban_104_178.symm, (List.forall_mem_cons.mpr ⟨used_ban_178_218, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good179 : NeighborGood 179 := by
  change ∀ s ∈ [80, 82, 83, 104, 218], NatPairBanned 179 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_80_179.symm, (List.forall_mem_cons.mpr ⟨used_ban_82_179.symm, (List.forall_mem_cons.mpr ⟨used_ban_83_179.symm, (List.forall_mem_cons.mpr ⟨used_ban_104_179.symm, (List.forall_mem_cons.mpr ⟨used_ban_179_218, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good180 : NeighborGood 180 := by
  change ∀ s ∈ [41, 48, 50, 51, 52, 53, 115, 116, 117, 118, 122, 123, 124, 125, 127, 128, 129, 130, 143, 144, 158, 162, 194, 197], NatPairBanned 180 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_41_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_48_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_50_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_51_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_52_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_53_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_115_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_116_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_117_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_118_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_122_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_123_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_124_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_125_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_127_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_128_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_129_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_130_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_143_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_144_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_158_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_162_180.symm, (List.forall_mem_cons.mpr ⟨used_ban_180_194, (List.forall_mem_cons.mpr ⟨used_ban_180_197, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good181 : NeighborGood 181 := by
  change ∀ s ∈ [48, 50, 51, 114, 115, 116, 117, 119, 120, 122, 123, 127, 158, 162, 194, 197], NatPairBanned 181 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_48_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_50_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_51_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_114_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_115_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_116_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_117_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_119_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_120_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_122_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_123_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_127_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_158_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_162_181.symm, (List.forall_mem_cons.mpr ⟨used_ban_181_194, (List.forall_mem_cons.mpr ⟨used_ban_181_197, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good182 : NeighborGood 182 := by
  change ∀ s ∈ [112, 124, 125, 190], NatPairBanned 182 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_112_182.symm, (List.forall_mem_cons.mpr ⟨used_ban_124_182.symm, (List.forall_mem_cons.mpr ⟨used_ban_125_182.symm, (List.forall_mem_cons.mpr ⟨used_ban_182_190, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good183 : NeighborGood 183 := by
  change ∀ s ∈ [112, 114, 119, 120, 124, 125, 155, 190, 191, 193], NatPairBanned 183 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_112_183.symm, (List.forall_mem_cons.mpr ⟨used_ban_114_183.symm, (List.forall_mem_cons.mpr ⟨used_ban_119_183.symm, (List.forall_mem_cons.mpr ⟨used_ban_120_183.symm, (List.forall_mem_cons.mpr ⟨used_ban_124_183.symm, (List.forall_mem_cons.mpr ⟨used_ban_125_183.symm, (List.forall_mem_cons.mpr ⟨used_ban_155_183.symm, (List.forall_mem_cons.mpr ⟨used_ban_183_190, (List.forall_mem_cons.mpr ⟨used_ban_183_191, (List.forall_mem_cons.mpr ⟨used_ban_183_193, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good184 : NeighborGood 184 := by
  change ∀ s ∈ [113], NatPairBanned 184 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_113_184.symm, List.forall_mem_nil _⟩)
theorem neighbor_good185 : NeighborGood 185 := by
  change ∀ s ∈ [112, 117, 190, 197], NatPairBanned 185 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_112_185.symm, (List.forall_mem_cons.mpr ⟨used_ban_117_185.symm, (List.forall_mem_cons.mpr ⟨used_ban_185_190, (List.forall_mem_cons.mpr ⟨used_ban_185_197, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good186 : NeighborGood 186 := by
  change ∀ s ∈ [117, 122, 123], NatPairBanned 186 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_117_186.symm, (List.forall_mem_cons.mpr ⟨used_ban_122_186.symm, (List.forall_mem_cons.mpr ⟨used_ban_123_186.symm, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good187 : NeighborGood 187 := by
  change ∀ s ∈ [83, 133, 135, 137, 139, 164], NatPairBanned 187 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_83_187.symm, (List.forall_mem_cons.mpr ⟨used_ban_133_187.symm, (List.forall_mem_cons.mpr ⟨used_ban_135_187.symm, (List.forall_mem_cons.mpr ⟨used_ban_137_187.symm, (List.forall_mem_cons.mpr ⟨used_ban_139_187.symm, (List.forall_mem_cons.mpr ⟨used_ban_164_187.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good188 : NeighborGood 188 := by
  change ∀ s ∈ [], NatPairBanned 188 s
  exact List.forall_mem_nil _
theorem neighbor_good189 : NeighborGood 189 := by
  change ∀ s ∈ [80, 82, 83, 84, 86, 130, 134, 135, 136, 137, 138, 139, 145, 146, 147, 148, 149, 156, 157, 159, 161, 162, 163, 165, 204, 208, 209, 210, 219], NatPairBanned 189 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_80_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_82_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_83_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_84_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_86_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_130_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_134_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_135_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_136_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_137_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_138_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_139_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_145_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_146_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_147_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_148_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_149_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_156_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_157_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_159_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_161_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_162_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_163_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_165_189.symm, (List.forall_mem_cons.mpr ⟨used_ban_189_204, (List.forall_mem_cons.mpr ⟨used_ban_189_208, (List.forall_mem_cons.mpr ⟨used_ban_189_209, (List.forall_mem_cons.mpr ⟨used_ban_189_210, (List.forall_mem_cons.mpr ⟨used_ban_189_219, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good190 : NeighborGood 190 := by
  change ∀ s ∈ [115, 117, 120, 123, 182, 183, 185], NatPairBanned 190 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_115_190.symm, (List.forall_mem_cons.mpr ⟨used_ban_117_190.symm, (List.forall_mem_cons.mpr ⟨used_ban_120_190.symm, (List.forall_mem_cons.mpr ⟨used_ban_123_190.symm, (List.forall_mem_cons.mpr ⟨used_ban_182_190.symm, (List.forall_mem_cons.mpr ⟨used_ban_183_190.symm, (List.forall_mem_cons.mpr ⟨used_ban_185_190.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good191 : NeighborGood 191 := by
  change ∀ s ∈ [83, 127, 131, 133, 135, 137, 139, 158, 183], NatPairBanned 191 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_83_191.symm, (List.forall_mem_cons.mpr ⟨used_ban_127_191.symm, (List.forall_mem_cons.mpr ⟨used_ban_131_191.symm, (List.forall_mem_cons.mpr ⟨used_ban_133_191.symm, (List.forall_mem_cons.mpr ⟨used_ban_135_191.symm, (List.forall_mem_cons.mpr ⟨used_ban_137_191.symm, (List.forall_mem_cons.mpr ⟨used_ban_139_191.symm, (List.forall_mem_cons.mpr ⟨used_ban_158_191.symm, (List.forall_mem_cons.mpr ⟨used_ban_183_191.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbors_range11 : AllRange NeighborGood 176 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good176, (List.forall_mem_cons.mpr ⟨neighbor_good177, (List.forall_mem_cons.mpr ⟨neighbor_good178, (List.forall_mem_cons.mpr ⟨neighbor_good179, (List.forall_mem_cons.mpr ⟨neighbor_good180, (List.forall_mem_cons.mpr ⟨neighbor_good181, (List.forall_mem_cons.mpr ⟨neighbor_good182, (List.forall_mem_cons.mpr ⟨neighbor_good183, (List.forall_mem_cons.mpr ⟨neighbor_good184, (List.forall_mem_cons.mpr ⟨neighbor_good185, (List.forall_mem_cons.mpr ⟨neighbor_good186, (List.forall_mem_cons.mpr ⟨neighbor_good187, (List.forall_mem_cons.mpr ⟨neighbor_good188, (List.forall_mem_cons.mpr ⟨neighbor_good189, (List.forall_mem_cons.mpr ⟨neighbor_good190, (List.forall_mem_cons.mpr ⟨neighbor_good191, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range11
