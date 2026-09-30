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
theorem neighbor_good80 : NeighborGood 80 := by
  change ∀ s ∈ [28, 30, 32, 179, 189], NatPairBanned 80 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_28_80.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_80.symm, (List.forall_mem_cons.mpr ⟨used_ban_32_80.symm, (List.forall_mem_cons.mpr ⟨used_ban_80_179, (List.forall_mem_cons.mpr ⟨used_ban_80_189, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good81 : NeighborGood 81 := by
  change ∀ s ∈ [30], NatPairBanned 81 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_30_81.symm, List.forall_mem_nil _⟩)
theorem neighbor_good82 : NeighborGood 82 := by
  change ∀ s ∈ [26, 28, 30, 32, 51, 65, 179, 189], NatPairBanned 82 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_26_82.symm, (List.forall_mem_cons.mpr ⟨used_ban_28_82.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_82.symm, (List.forall_mem_cons.mpr ⟨used_ban_32_82.symm, (List.forall_mem_cons.mpr ⟨used_ban_51_82.symm, (List.forall_mem_cons.mpr ⟨used_ban_65_82.symm, (List.forall_mem_cons.mpr ⟨used_ban_82_179, (List.forall_mem_cons.mpr ⟨used_ban_82_189, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good83 : NeighborGood 83 := by
  change ∀ s ∈ [30, 179, 187, 189, 191], NatPairBanned 83 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_30_83.symm, (List.forall_mem_cons.mpr ⟨used_ban_83_179, (List.forall_mem_cons.mpr ⟨used_ban_83_187, (List.forall_mem_cons.mpr ⟨used_ban_83_189, (List.forall_mem_cons.mpr ⟨used_ban_83_191, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good84 : NeighborGood 84 := by
  change ∀ s ∈ [28, 30, 32, 68, 189], NatPairBanned 84 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_28_84.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_84.symm, (List.forall_mem_cons.mpr ⟨used_ban_32_84.symm, (List.forall_mem_cons.mpr ⟨used_ban_68_84.symm, (List.forall_mem_cons.mpr ⟨used_ban_84_189, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good85 : NeighborGood 85 := by
  change ∀ s ∈ [30, 68, 193], NatPairBanned 85 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_30_85.symm, (List.forall_mem_cons.mpr ⟨used_ban_68_85.symm, (List.forall_mem_cons.mpr ⟨used_ban_85_193, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good86 : NeighborGood 86 := by
  change ∀ s ∈ [26, 28, 32, 65, 70, 143, 189], NatPairBanned 86 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_26_86.symm, (List.forall_mem_cons.mpr ⟨used_ban_28_86.symm, (List.forall_mem_cons.mpr ⟨used_ban_32_86.symm, (List.forall_mem_cons.mpr ⟨used_ban_65_86.symm, (List.forall_mem_cons.mpr ⟨used_ban_70_86.symm, (List.forall_mem_cons.mpr ⟨used_ban_86_143, (List.forall_mem_cons.mpr ⟨used_ban_86_189, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good87 : NeighborGood 87 := by
  change ∀ s ∈ [], NatPairBanned 87 s
  exact List.forall_mem_nil _
theorem neighbor_good88 : NeighborGood 88 := by
  change ∀ s ∈ [28, 176, 209, 218], NatPairBanned 88 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_28_88.symm, (List.forall_mem_cons.mpr ⟨used_ban_88_176, (List.forall_mem_cons.mpr ⟨used_ban_88_209, (List.forall_mem_cons.mpr ⟨used_ban_88_218, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good89 : NeighborGood 89 := by
  change ∀ s ∈ [30, 33, 39], NatPairBanned 89 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_30_89.symm, (List.forall_mem_cons.mpr ⟨used_ban_33_89.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_89.symm, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good90 : NeighborGood 90 := by
  change ∀ s ∈ [39], NatPairBanned 90 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_39_90.symm, List.forall_mem_nil _⟩)
theorem neighbor_good91 : NeighborGood 91 := by
  change ∀ s ∈ [33, 39, 104], NatPairBanned 91 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_33_91.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_91.symm, (List.forall_mem_cons.mpr ⟨used_ban_91_104, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good92 : NeighborGood 92 := by
  change ∀ s ∈ [27, 28, 29, 38, 39, 101, 104, 108, 171, 172, 177, 209, 218], NatPairBanned 92 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_27_92.symm, (List.forall_mem_cons.mpr ⟨used_ban_28_92.symm, (List.forall_mem_cons.mpr ⟨used_ban_29_92.symm, (List.forall_mem_cons.mpr ⟨used_ban_38_92.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_92.symm, (List.forall_mem_cons.mpr ⟨used_ban_92_101, (List.forall_mem_cons.mpr ⟨used_ban_92_104, (List.forall_mem_cons.mpr ⟨used_ban_92_108, (List.forall_mem_cons.mpr ⟨used_ban_92_171, (List.forall_mem_cons.mpr ⟨used_ban_92_172, (List.forall_mem_cons.mpr ⟨used_ban_92_177, (List.forall_mem_cons.mpr ⟨used_ban_92_209, (List.forall_mem_cons.mpr ⟨used_ban_92_218, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good93 : NeighborGood 93 := by
  change ∀ s ∈ [], NatPairBanned 93 s
  exact List.forall_mem_nil _
theorem neighbor_good94 : NeighborGood 94 := by
  change ∀ s ∈ [14, 22, 25, 33, 36, 37, 39], NatPairBanned 94 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_14_94.symm, (List.forall_mem_cons.mpr ⟨used_ban_22_94.symm, (List.forall_mem_cons.mpr ⟨used_ban_25_94.symm, (List.forall_mem_cons.mpr ⟨used_ban_33_94.symm, (List.forall_mem_cons.mpr ⟨used_ban_36_94.symm, (List.forall_mem_cons.mpr ⟨used_ban_37_94.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_94.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good95 : NeighborGood 95 := by
  change ∀ s ∈ [33, 36, 37, 39], NatPairBanned 95 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_33_95.symm, (List.forall_mem_cons.mpr ⟨used_ban_36_95.symm, (List.forall_mem_cons.mpr ⟨used_ban_37_95.symm, (List.forall_mem_cons.mpr ⟨used_ban_39_95.symm, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbors_range5 : AllRange NeighborGood 80 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good80, (List.forall_mem_cons.mpr ⟨neighbor_good81, (List.forall_mem_cons.mpr ⟨neighbor_good82, (List.forall_mem_cons.mpr ⟨neighbor_good83, (List.forall_mem_cons.mpr ⟨neighbor_good84, (List.forall_mem_cons.mpr ⟨neighbor_good85, (List.forall_mem_cons.mpr ⟨neighbor_good86, (List.forall_mem_cons.mpr ⟨neighbor_good87, (List.forall_mem_cons.mpr ⟨neighbor_good88, (List.forall_mem_cons.mpr ⟨neighbor_good89, (List.forall_mem_cons.mpr ⟨neighbor_good90, (List.forall_mem_cons.mpr ⟨neighbor_good91, (List.forall_mem_cons.mpr ⟨neighbor_good92, (List.forall_mem_cons.mpr ⟨neighbor_good93, (List.forall_mem_cons.mpr ⟨neighbor_good94, (List.forall_mem_cons.mpr ⟨neighbor_good95, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range5
