import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts2
import ElevenSquare.Pending.S07_SelectedBanFacts3
import ElevenSquare.Pending.S07_SelectedBanFacts4
import ElevenSquare.Pending.S07_SelectedBanFacts5
import ElevenSquare.Pending.S07_SelectedBanFacts6
import ElevenSquare.Pending.S07_SelectedBanFacts7
import ElevenSquare.Pending.S07_SelectedBanFacts8
import ElevenSquare.Pending.S07_SelectedBanFacts9
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good96 : NeighborGood 96 := by
  change ∀ s ∈ [29, 33, 38, 39], NatPairBanned 96 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_29_96.symm, (List.forall_mem_cons.mpr ⟨used_ban_33_96.symm, (List.forall_mem_cons.mpr ⟨used_ban_38_96.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_96.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good97 : NeighborGood 97 := by
  change ∀ s ∈ [27, 33, 38, 39], NatPairBanned 97 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_27_97.symm, (List.forall_mem_cons.mpr ⟨used_ban_33_97.symm, (List.forall_mem_cons.mpr ⟨used_ban_38_97.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_97.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good98 : NeighborGood 98 := by
  change ∀ s ∈ [28, 29], NatPairBanned 98 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_28_98.symm, (List.forall_mem_cons.mpr ⟨used_ban_29_98.symm, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good99 : NeighborGood 99 := by
  change ∀ s ∈ [29, 36, 38], NatPairBanned 99 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_29_99.symm, (List.forall_mem_cons.mpr ⟨used_ban_36_99.symm, (List.forall_mem_cons.mpr ⟨used_ban_38_99.symm, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good100 : NeighborGood 100 := by
  change ∀ s ∈ [27, 28, 36, 38], NatPairBanned 100 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_27_100.symm, (List.forall_mem_cons.mpr ⟨used_ban_28_100.symm, (List.forall_mem_cons.mpr ⟨used_ban_36_100.symm, (List.forall_mem_cons.mpr ⟨used_ban_38_100.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good101 : NeighborGood 101 := by
  change ∀ s ∈ [33, 39, 77, 92, 177], NatPairBanned 101 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_33_101.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_101.symm, (List.forall_mem_cons.mpr ⟨used_ban_77_101.symm, (List.forall_mem_cons.mpr ⟨used_ban_92_101.symm, (List.forall_mem_cons.mpr ⟨used_ban_101_177, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good102 : NeighborGood 102 := by
  change ∀ s ∈ [21, 29, 33, 34, 38, 39], NatPairBanned 102 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_21_102.symm, (List.forall_mem_cons.mpr ⟨used_ban_29_102.symm, (List.forall_mem_cons.mpr ⟨used_ban_33_102.symm, (List.forall_mem_cons.mpr ⟨used_ban_34_102.symm, (List.forall_mem_cons.mpr ⟨used_ban_38_102.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_102.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good103 : NeighborGood 103 := by
  change ∀ s ∈ [38, 39, 178], NatPairBanned 103 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_38_103.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_103.symm, (List.forall_mem_cons.mpr ⟨used_ban_103_178, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good104 : NeighborGood 104 := by
  change ∀ s ∈ [29, 38, 39, 79, 91, 92, 174, 176, 178, 179], NatPairBanned 104 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_29_104.symm, (List.forall_mem_cons.mpr ⟨used_ban_38_104.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_104.symm, (List.forall_mem_cons.mpr ⟨used_ban_79_104.symm, (List.forall_mem_cons.mpr ⟨used_ban_91_104.symm, (List.forall_mem_cons.mpr ⟨used_ban_92_104.symm, (List.forall_mem_cons.mpr ⟨used_ban_104_174, (List.forall_mem_cons.mpr ⟨used_ban_104_176, (List.forall_mem_cons.mpr ⟨used_ban_104_178, (List.forall_mem_cons.mpr ⟨used_ban_104_179, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good105 : NeighborGood 105 := by
  change ∀ s ∈ [27, 28, 36, 38], NatPairBanned 105 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_27_105.symm, (List.forall_mem_cons.mpr ⟨used_ban_28_105.symm, (List.forall_mem_cons.mpr ⟨used_ban_36_105.symm, (List.forall_mem_cons.mpr ⟨used_ban_38_105.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good106 : NeighborGood 106 := by
  change ∀ s ∈ [35], NatPairBanned 106 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_35_106.symm, List.forall_mem_nil _⟩)
theorem neighbor_good107 : NeighborGood 107 := by
  change ∀ s ∈ [14, 21, 34, 36, 37], NatPairBanned 107 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_14_107.symm, (List.forall_mem_cons.mpr ⟨used_ban_21_107.symm, (List.forall_mem_cons.mpr ⟨used_ban_34_107.symm, (List.forall_mem_cons.mpr ⟨used_ban_36_107.symm, (List.forall_mem_cons.mpr ⟨used_ban_37_107.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good108 : NeighborGood 108 := by
  change ∀ s ∈ [21, 57, 61, 92, 168], NatPairBanned 108 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_21_108.symm, (List.forall_mem_cons.mpr ⟨used_ban_57_108.symm, (List.forall_mem_cons.mpr ⟨used_ban_61_108.symm, (List.forall_mem_cons.mpr ⟨used_ban_92_108.symm, (List.forall_mem_cons.mpr ⟨used_ban_108_168, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good109 : NeighborGood 109 := by
  change ∀ s ∈ [], NatPairBanned 109 s
  exact List.forall_mem_nil _
theorem neighbor_good110 : NeighborGood 110 := by
  change ∀ s ∈ [], NatPairBanned 110 s
  exact List.forall_mem_nil _
theorem neighbor_good111 : NeighborGood 111 := by
  change ∀ s ∈ [51, 127, 158, 162], NatPairBanned 111 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_51_111.symm, (List.forall_mem_cons.mpr ⟨used_ban_111_127, (List.forall_mem_cons.mpr ⟨used_ban_111_158, (List.forall_mem_cons.mpr ⟨used_ban_111_162, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbors_range6 : AllRange NeighborGood 96 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good96, (List.forall_mem_cons.mpr ⟨neighbor_good97, (List.forall_mem_cons.mpr ⟨neighbor_good98, (List.forall_mem_cons.mpr ⟨neighbor_good99, (List.forall_mem_cons.mpr ⟨neighbor_good100, (List.forall_mem_cons.mpr ⟨neighbor_good101, (List.forall_mem_cons.mpr ⟨neighbor_good102, (List.forall_mem_cons.mpr ⟨neighbor_good103, (List.forall_mem_cons.mpr ⟨neighbor_good104, (List.forall_mem_cons.mpr ⟨neighbor_good105, (List.forall_mem_cons.mpr ⟨neighbor_good106, (List.forall_mem_cons.mpr ⟨neighbor_good107, (List.forall_mem_cons.mpr ⟨neighbor_good108, (List.forall_mem_cons.mpr ⟨neighbor_good109, (List.forall_mem_cons.mpr ⟨neighbor_good110, (List.forall_mem_cons.mpr ⟨neighbor_good111, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range6
