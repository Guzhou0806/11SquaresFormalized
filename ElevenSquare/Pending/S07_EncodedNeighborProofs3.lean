import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts0
import ElevenSquare.Pending.S07_SelectedBanFacts1
import ElevenSquare.Pending.S07_SelectedBanFacts2
import ElevenSquare.Pending.S07_SelectedBanFacts3
import ElevenSquare.Pending.S07_SelectedBanFacts4
import ElevenSquare.Pending.S07_SelectedBanFacts5
import ElevenSquare.Pending.S07_SelectedBanFacts6
import ElevenSquare.Pending.S07_SelectedBanFacts7
import ElevenSquare.Pending.S07_SelectedBanFacts8
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good48 : NeighborGood 48 := by
  change ∀ s ∈ [5, 180, 181], NatPairBanned 48 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_5_48.symm, (List.forall_mem_cons.mpr ⟨used_ban_48_180, (List.forall_mem_cons.mpr ⟨used_ban_48_181, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good49 : NeighborGood 49 := by
  change ∀ s ∈ [], NatPairBanned 49 s
  exact List.forall_mem_nil _
theorem neighbor_good50 : NeighborGood 50 := by
  change ∀ s ∈ [180, 181], NatPairBanned 50 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_50_180, (List.forall_mem_cons.mpr ⟨used_ban_50_181, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good51 : NeighborGood 51 := by
  change ∀ s ∈ [82, 111, 180, 181], NatPairBanned 51 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_51_82, (List.forall_mem_cons.mpr ⟨used_ban_51_111, (List.forall_mem_cons.mpr ⟨used_ban_51_180, (List.forall_mem_cons.mpr ⟨used_ban_51_181, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good52 : NeighborGood 52 := by
  change ∀ s ∈ [5, 180], NatPairBanned 52 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_5_52.symm, (List.forall_mem_cons.mpr ⟨used_ban_52_180, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good53 : NeighborGood 53 := by
  change ∀ s ∈ [5, 180], NatPairBanned 53 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_5_53.symm, (List.forall_mem_cons.mpr ⟨used_ban_53_180, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good54 : NeighborGood 54 := by
  change ∀ s ∈ [3, 7, 8, 12, 18, 19, 26, 30], NatPairBanned 54 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_3_54.symm, (List.forall_mem_cons.mpr ⟨used_ban_7_54.symm, (List.forall_mem_cons.mpr ⟨used_ban_8_54.symm, (List.forall_mem_cons.mpr ⟨used_ban_12_54.symm, (List.forall_mem_cons.mpr ⟨used_ban_18_54.symm, (List.forall_mem_cons.mpr ⟨used_ban_19_54.symm, (List.forall_mem_cons.mpr ⟨used_ban_26_54.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_54.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good55 : NeighborGood 55 := by
  change ∀ s ∈ [14, 32], NatPairBanned 55 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_14_55.symm, (List.forall_mem_cons.mpr ⟨used_ban_32_55.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good56 : NeighborGood 56 := by
  change ∀ s ∈ [4, 12, 19, 30], NatPairBanned 56 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_4_56.symm, (List.forall_mem_cons.mpr ⟨used_ban_12_56.symm, (List.forall_mem_cons.mpr ⟨used_ban_19_56.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_56.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good57 : NeighborGood 57 := by
  change ∀ s ∈ [12, 13, 14, 19, 30, 38, 39, 108], NatPairBanned 57 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_12_57.symm, (List.forall_mem_cons.mpr ⟨used_ban_13_57.symm, (List.forall_mem_cons.mpr ⟨used_ban_14_57.symm, (List.forall_mem_cons.mpr ⟨used_ban_19_57.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_57.symm, (List.forall_mem_cons.mpr ⟨used_ban_38_57.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_57.symm, (List.forall_mem_cons.mpr ⟨used_ban_57_108, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good58 : NeighborGood 58 := by
  change ∀ s ∈ [26, 30], NatPairBanned 58 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_26_58.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_58.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good59 : NeighborGood 59 := by
  change ∀ s ∈ [14, 26], NatPairBanned 59 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_14_59.symm, (List.forall_mem_cons.mpr ⟨used_ban_26_59.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good60 : NeighborGood 60 := by
  change ∀ s ∈ [26, 30], NatPairBanned 60 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_26_60.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_60.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good61 : NeighborGood 61 := by
  change ∀ s ∈ [26, 28, 38, 39, 108], NatPairBanned 61 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_26_61.symm, (List.forall_mem_cons.mpr ⟨used_ban_28_61.symm, (List.forall_mem_cons.mpr ⟨used_ban_38_61.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_61.symm, (List.forall_mem_cons.mpr ⟨used_ban_61_108, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good62 : NeighborGood 62 := by
  change ∀ s ∈ [17, 25, 26, 30], NatPairBanned 62 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_17_62.symm, (List.forall_mem_cons.mpr ⟨used_ban_25_62.symm, (List.forall_mem_cons.mpr ⟨used_ban_26_62.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_62.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good63 : NeighborGood 63 := by
  change ∀ s ∈ [17, 25, 26, 30], NatPairBanned 63 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_17_63.symm, (List.forall_mem_cons.mpr ⟨used_ban_25_63.symm, (List.forall_mem_cons.mpr ⟨used_ban_26_63.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_63.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbors_range3 : AllRange NeighborGood 48 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good48, (List.forall_mem_cons.mpr ⟨neighbor_good49, (List.forall_mem_cons.mpr ⟨neighbor_good50, (List.forall_mem_cons.mpr ⟨neighbor_good51, (List.forall_mem_cons.mpr ⟨neighbor_good52, (List.forall_mem_cons.mpr ⟨neighbor_good53, (List.forall_mem_cons.mpr ⟨neighbor_good54, (List.forall_mem_cons.mpr ⟨neighbor_good55, (List.forall_mem_cons.mpr ⟨neighbor_good56, (List.forall_mem_cons.mpr ⟨neighbor_good57, (List.forall_mem_cons.mpr ⟨neighbor_good58, (List.forall_mem_cons.mpr ⟨neighbor_good59, (List.forall_mem_cons.mpr ⟨neighbor_good60, (List.forall_mem_cons.mpr ⟨neighbor_good61, (List.forall_mem_cons.mpr ⟨neighbor_good62, (List.forall_mem_cons.mpr ⟨neighbor_good63, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range3
