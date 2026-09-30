import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts0
import ElevenSquare.Pending.S07_SelectedBanFacts1
import ElevenSquare.Pending.S07_SelectedBanFacts2
import ElevenSquare.Pending.S07_SelectedBanFacts3
import ElevenSquare.Pending.S07_SelectedBanFacts5
import ElevenSquare.Pending.S07_SelectedBanFacts6
import ElevenSquare.Pending.S07_SelectedBanFacts8
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good64 : NeighborGood 64 := by
  change ∀ s ∈ [0, 14, 15, 36], NatPairBanned 64 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_0_64.symm, (List.forall_mem_cons.mpr ⟨used_ban_14_64.symm, (List.forall_mem_cons.mpr ⟨used_ban_15_64.symm, (List.forall_mem_cons.mpr ⟨used_ban_36_64.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good65 : NeighborGood 65 := by
  change ∀ s ∈ [1, 9, 25, 82, 86, 134], NatPairBanned 65 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_1_65.symm, (List.forall_mem_cons.mpr ⟨used_ban_9_65.symm, (List.forall_mem_cons.mpr ⟨used_ban_25_65.symm, (List.forall_mem_cons.mpr ⟨used_ban_65_82, (List.forall_mem_cons.mpr ⟨used_ban_65_86, (List.forall_mem_cons.mpr ⟨used_ban_65_134, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good66 : NeighborGood 66 := by
  change ∀ s ∈ [0, 15], NatPairBanned 66 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_0_66.symm, (List.forall_mem_cons.mpr ⟨used_ban_15_66.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good67 : NeighborGood 67 := by
  change ∀ s ∈ [0, 1, 12, 15, 16, 19], NatPairBanned 67 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_0_67.symm, (List.forall_mem_cons.mpr ⟨used_ban_1_67.symm, (List.forall_mem_cons.mpr ⟨used_ban_12_67.symm, (List.forall_mem_cons.mpr ⟨used_ban_15_67.symm, (List.forall_mem_cons.mpr ⟨used_ban_16_67.symm, (List.forall_mem_cons.mpr ⟨used_ban_19_67.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good68 : NeighborGood 68 := by
  change ∀ s ∈ [0, 1, 26, 77, 84, 85, 136, 137, 139], NatPairBanned 68 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_0_68.symm, (List.forall_mem_cons.mpr ⟨used_ban_1_68.symm, (List.forall_mem_cons.mpr ⟨used_ban_26_68.symm, (List.forall_mem_cons.mpr ⟨used_ban_68_77, (List.forall_mem_cons.mpr ⟨used_ban_68_84, (List.forall_mem_cons.mpr ⟨used_ban_68_85, (List.forall_mem_cons.mpr ⟨used_ban_68_136, (List.forall_mem_cons.mpr ⟨used_ban_68_137, (List.forall_mem_cons.mpr ⟨used_ban_68_139, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good69 : NeighborGood 69 := by
  change ∀ s ∈ [1, 139], NatPairBanned 69 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_1_69.symm, (List.forall_mem_cons.mpr ⟨used_ban_69_139, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good70 : NeighborGood 70 := by
  change ∀ s ∈ [1, 6, 9, 30, 79, 86, 144], NatPairBanned 70 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_1_70.symm, (List.forall_mem_cons.mpr ⟨used_ban_6_70.symm, (List.forall_mem_cons.mpr ⟨used_ban_9_70.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_70.symm, (List.forall_mem_cons.mpr ⟨used_ban_70_79, (List.forall_mem_cons.mpr ⟨used_ban_70_86, (List.forall_mem_cons.mpr ⟨used_ban_70_144, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good71 : NeighborGood 71 := by
  change ∀ s ∈ [15, 26, 30], NatPairBanned 71 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_15_71.symm, (List.forall_mem_cons.mpr ⟨used_ban_26_71.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_71.symm, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good72 : NeighborGood 72 := by
  change ∀ s ∈ [12, 15, 16, 17, 18, 19, 25, 26, 30], NatPairBanned 72 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_12_72.symm, (List.forall_mem_cons.mpr ⟨used_ban_15_72.symm, (List.forall_mem_cons.mpr ⟨used_ban_16_72.symm, (List.forall_mem_cons.mpr ⟨used_ban_17_72.symm, (List.forall_mem_cons.mpr ⟨used_ban_18_72.symm, (List.forall_mem_cons.mpr ⟨used_ban_19_72.symm, (List.forall_mem_cons.mpr ⟨used_ban_25_72.symm, (List.forall_mem_cons.mpr ⟨used_ban_26_72.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_72.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good73 : NeighborGood 73 := by
  change ∀ s ∈ [17, 25, 26, 30], NatPairBanned 73 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_17_73.symm, (List.forall_mem_cons.mpr ⟨used_ban_25_73.symm, (List.forall_mem_cons.mpr ⟨used_ban_26_73.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_73.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good74 : NeighborGood 74 := by
  change ∀ s ∈ [17, 25, 26, 30], NatPairBanned 74 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_17_74.symm, (List.forall_mem_cons.mpr ⟨used_ban_25_74.symm, (List.forall_mem_cons.mpr ⟨used_ban_26_74.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_74.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good75 : NeighborGood 75 := by
  change ∀ s ∈ [33, 39, 138, 218], NatPairBanned 75 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_33_75.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_75.symm, (List.forall_mem_cons.mpr ⟨used_ban_75_138, (List.forall_mem_cons.mpr ⟨used_ban_75_218, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good76 : NeighborGood 76 := by
  change ∀ s ∈ [33, 39], NatPairBanned 76 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_33_76.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_76.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good77 : NeighborGood 77 := by
  change ∀ s ∈ [68, 101], NatPairBanned 77 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_68_77.symm, (List.forall_mem_cons.mpr ⟨used_ban_77_101, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good78 : NeighborGood 78 := by
  change ∀ s ∈ [], NatPairBanned 78 s
  exact List.forall_mem_nil _
theorem neighbor_good79 : NeighborGood 79 := by
  change ∀ s ∈ [21, 70, 104], NatPairBanned 79 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_21_79.symm, (List.forall_mem_cons.mpr ⟨used_ban_70_79.symm, (List.forall_mem_cons.mpr ⟨used_ban_79_104, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbors_range4 : AllRange NeighborGood 64 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good64, (List.forall_mem_cons.mpr ⟨neighbor_good65, (List.forall_mem_cons.mpr ⟨neighbor_good66, (List.forall_mem_cons.mpr ⟨neighbor_good67, (List.forall_mem_cons.mpr ⟨neighbor_good68, (List.forall_mem_cons.mpr ⟨neighbor_good69, (List.forall_mem_cons.mpr ⟨neighbor_good70, (List.forall_mem_cons.mpr ⟨neighbor_good71, (List.forall_mem_cons.mpr ⟨neighbor_good72, (List.forall_mem_cons.mpr ⟨neighbor_good73, (List.forall_mem_cons.mpr ⟨neighbor_good74, (List.forall_mem_cons.mpr ⟨neighbor_good75, (List.forall_mem_cons.mpr ⟨neighbor_good76, (List.forall_mem_cons.mpr ⟨neighbor_good77, (List.forall_mem_cons.mpr ⟨neighbor_good78, (List.forall_mem_cons.mpr ⟨neighbor_good79, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range4
