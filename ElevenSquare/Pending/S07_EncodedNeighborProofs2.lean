import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts0
import ElevenSquare.Pending.S07_SelectedBanFacts1
import ElevenSquare.Pending.S07_SelectedBanFacts2
import ElevenSquare.Pending.S07_SelectedBanFacts3
import ElevenSquare.Pending.S07_SelectedBanFacts4
import ElevenSquare.Pending.S07_SelectedBanFacts5
import ElevenSquare.Pending.S07_SelectedBanFacts6
import ElevenSquare.Pending.S07_SelectedBanFacts7
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good32 : NeighborGood 32 := by
  change ∀ s ∈ [12, 55, 80, 82, 84, 86], NatPairBanned 32 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_12_32.symm, (List.forall_mem_cons.mpr ⟨used_ban_32_55, (List.forall_mem_cons.mpr ⟨used_ban_32_80, (List.forall_mem_cons.mpr ⟨used_ban_32_82, (List.forall_mem_cons.mpr ⟨used_ban_32_84, (List.forall_mem_cons.mpr ⟨used_ban_32_86, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good33 : NeighborGood 33 := by
  change ∀ s ∈ [75, 76, 89, 91, 94, 95, 96, 97, 101, 102], NatPairBanned 33 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_33_75, (List.forall_mem_cons.mpr ⟨used_ban_33_76, (List.forall_mem_cons.mpr ⟨used_ban_33_89, (List.forall_mem_cons.mpr ⟨used_ban_33_91, (List.forall_mem_cons.mpr ⟨used_ban_33_94, (List.forall_mem_cons.mpr ⟨used_ban_33_95, (List.forall_mem_cons.mpr ⟨used_ban_33_96, (List.forall_mem_cons.mpr ⟨used_ban_33_97, (List.forall_mem_cons.mpr ⟨used_ban_33_101, (List.forall_mem_cons.mpr ⟨used_ban_33_102, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good34 : NeighborGood 34 := by
  change ∀ s ∈ [22, 29, 102, 107], NatPairBanned 34 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_22_34.symm, (List.forall_mem_cons.mpr ⟨used_ban_29_34.symm, (List.forall_mem_cons.mpr ⟨used_ban_34_102, (List.forall_mem_cons.mpr ⟨used_ban_34_107, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good35 : NeighborGood 35 := by
  change ∀ s ∈ [106], NatPairBanned 35 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_35_106, List.forall_mem_nil _⟩)
theorem neighbor_good36 : NeighborGood 36 := by
  change ∀ s ∈ [26, 28, 29, 64, 94, 95, 99, 100, 105, 107], NatPairBanned 36 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_26_36.symm, (List.forall_mem_cons.mpr ⟨used_ban_28_36.symm, (List.forall_mem_cons.mpr ⟨used_ban_29_36.symm, (List.forall_mem_cons.mpr ⟨used_ban_36_64, (List.forall_mem_cons.mpr ⟨used_ban_36_94, (List.forall_mem_cons.mpr ⟨used_ban_36_95, (List.forall_mem_cons.mpr ⟨used_ban_36_99, (List.forall_mem_cons.mpr ⟨used_ban_36_100, (List.forall_mem_cons.mpr ⟨used_ban_36_105, (List.forall_mem_cons.mpr ⟨used_ban_36_107, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good37 : NeighborGood 37 := by
  change ∀ s ∈ [29, 94, 95, 107], NatPairBanned 37 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_29_37.symm, (List.forall_mem_cons.mpr ⟨used_ban_37_94, (List.forall_mem_cons.mpr ⟨used_ban_37_95, (List.forall_mem_cons.mpr ⟨used_ban_37_107, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good38 : NeighborGood 38 := by
  change ∀ s ∈ [22, 25, 57, 61, 92, 96, 97, 99, 100, 102, 103, 104, 105, 168, 169, 171], NatPairBanned 38 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_22_38.symm, (List.forall_mem_cons.mpr ⟨used_ban_25_38.symm, (List.forall_mem_cons.mpr ⟨used_ban_38_57, (List.forall_mem_cons.mpr ⟨used_ban_38_61, (List.forall_mem_cons.mpr ⟨used_ban_38_92, (List.forall_mem_cons.mpr ⟨used_ban_38_96, (List.forall_mem_cons.mpr ⟨used_ban_38_97, (List.forall_mem_cons.mpr ⟨used_ban_38_99, (List.forall_mem_cons.mpr ⟨used_ban_38_100, (List.forall_mem_cons.mpr ⟨used_ban_38_102, (List.forall_mem_cons.mpr ⟨used_ban_38_103, (List.forall_mem_cons.mpr ⟨used_ban_38_104, (List.forall_mem_cons.mpr ⟨used_ban_38_105, (List.forall_mem_cons.mpr ⟨used_ban_38_168, (List.forall_mem_cons.mpr ⟨used_ban_38_169, (List.forall_mem_cons.mpr ⟨used_ban_38_171, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good39 : NeighborGood 39 := by
  change ∀ s ∈ [22, 25, 57, 61, 75, 76, 89, 90, 91, 92, 94, 95, 96, 97, 101, 102, 103, 104, 166, 167, 168, 169, 171, 178], NatPairBanned 39 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_22_39.symm, (List.forall_mem_cons.mpr ⟨used_ban_25_39.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_57, (List.forall_mem_cons.mpr ⟨used_ban_39_61, (List.forall_mem_cons.mpr ⟨used_ban_39_75, (List.forall_mem_cons.mpr ⟨used_ban_39_76, (List.forall_mem_cons.mpr ⟨used_ban_39_89, (List.forall_mem_cons.mpr ⟨used_ban_39_90, (List.forall_mem_cons.mpr ⟨used_ban_39_91, (List.forall_mem_cons.mpr ⟨used_ban_39_92, (List.forall_mem_cons.mpr ⟨used_ban_39_94, (List.forall_mem_cons.mpr ⟨used_ban_39_95, (List.forall_mem_cons.mpr ⟨used_ban_39_96, (List.forall_mem_cons.mpr ⟨used_ban_39_97, (List.forall_mem_cons.mpr ⟨used_ban_39_101, (List.forall_mem_cons.mpr ⟨used_ban_39_102, (List.forall_mem_cons.mpr ⟨used_ban_39_103, (List.forall_mem_cons.mpr ⟨used_ban_39_104, (List.forall_mem_cons.mpr ⟨used_ban_39_166, (List.forall_mem_cons.mpr ⟨used_ban_39_167, (List.forall_mem_cons.mpr ⟨used_ban_39_168, (List.forall_mem_cons.mpr ⟨used_ban_39_169, (List.forall_mem_cons.mpr ⟨used_ban_39_171, (List.forall_mem_cons.mpr ⟨used_ban_39_178, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good40 : NeighborGood 40 := by
  change ∀ s ∈ [115, 136, 137, 139], NatPairBanned 40 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_40_115, (List.forall_mem_cons.mpr ⟨used_ban_40_136, (List.forall_mem_cons.mpr ⟨used_ban_40_137, (List.forall_mem_cons.mpr ⟨used_ban_40_139, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good41 : NeighborGood 41 := by
  change ∀ s ∈ [5, 115, 116, 180], NatPairBanned 41 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_5_41.symm, (List.forall_mem_cons.mpr ⟨used_ban_41_115, (List.forall_mem_cons.mpr ⟨used_ban_41_116, (List.forall_mem_cons.mpr ⟨used_ban_41_180, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good42 : NeighborGood 42 := by
  change ∀ s ∈ [118], NatPairBanned 42 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_42_118, List.forall_mem_nil _⟩)
theorem neighbor_good43 : NeighborGood 43 := by
  change ∀ s ∈ [19, 115], NatPairBanned 43 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_19_43.symm, (List.forall_mem_cons.mpr ⟨used_ban_43_115, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good44 : NeighborGood 44 := by
  change ∀ s ∈ [], NatPairBanned 44 s
  exact List.forall_mem_nil _
theorem neighbor_good45 : NeighborGood 45 := by
  change ∀ s ∈ [115], NatPairBanned 45 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_45_115, List.forall_mem_nil _⟩)
theorem neighbor_good46 : NeighborGood 46 := by
  change ∀ s ∈ [], NatPairBanned 46 s
  exact List.forall_mem_nil _
theorem neighbor_good47 : NeighborGood 47 := by
  change ∀ s ∈ [127], NatPairBanned 47 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_47_127, List.forall_mem_nil _⟩)
theorem neighbors_range2 : AllRange NeighborGood 32 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good32, (List.forall_mem_cons.mpr ⟨neighbor_good33, (List.forall_mem_cons.mpr ⟨neighbor_good34, (List.forall_mem_cons.mpr ⟨neighbor_good35, (List.forall_mem_cons.mpr ⟨neighbor_good36, (List.forall_mem_cons.mpr ⟨neighbor_good37, (List.forall_mem_cons.mpr ⟨neighbor_good38, (List.forall_mem_cons.mpr ⟨neighbor_good39, (List.forall_mem_cons.mpr ⟨neighbor_good40, (List.forall_mem_cons.mpr ⟨neighbor_good41, (List.forall_mem_cons.mpr ⟨neighbor_good42, (List.forall_mem_cons.mpr ⟨neighbor_good43, (List.forall_mem_cons.mpr ⟨neighbor_good44, (List.forall_mem_cons.mpr ⟨neighbor_good45, (List.forall_mem_cons.mpr ⟨neighbor_good46, (List.forall_mem_cons.mpr ⟨neighbor_good47, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range2
