import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts0
import ElevenSquare.Pending.S07_SelectedBanFacts1
import ElevenSquare.Pending.S07_SelectedBanFacts2
import ElevenSquare.Pending.S07_SelectedBanFacts3
import ElevenSquare.Pending.S07_SelectedBanFacts4
import ElevenSquare.Pending.S07_SelectedBanFacts5
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good16 : NeighborGood 16 := by
  change ∀ s ∈ [9, 67, 72], NatPairBanned 16 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_9_16.symm, (List.forall_mem_cons.mpr ⟨used_ban_16_67, (List.forall_mem_cons.mpr ⟨used_ban_16_72, List.forall_mem_nil _⟩)⟩)⟩)
theorem neighbor_good17 : NeighborGood 17 := by
  change ∀ s ∈ [3, 9, 10, 11, 24, 26, 62, 63, 72, 73, 74], NatPairBanned 17 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_3_17.symm, (List.forall_mem_cons.mpr ⟨used_ban_9_17.symm, (List.forall_mem_cons.mpr ⟨used_ban_10_17.symm, (List.forall_mem_cons.mpr ⟨used_ban_11_17.symm, (List.forall_mem_cons.mpr ⟨used_ban_17_24, (List.forall_mem_cons.mpr ⟨used_ban_17_26, (List.forall_mem_cons.mpr ⟨used_ban_17_62, (List.forall_mem_cons.mpr ⟨used_ban_17_63, (List.forall_mem_cons.mpr ⟨used_ban_17_72, (List.forall_mem_cons.mpr ⟨used_ban_17_73, (List.forall_mem_cons.mpr ⟨used_ban_17_74, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good18 : NeighborGood 18 := by
  change ∀ s ∈ [6, 9, 54, 72], NatPairBanned 18 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_6_18.symm, (List.forall_mem_cons.mpr ⟨used_ban_9_18.symm, (List.forall_mem_cons.mpr ⟨used_ban_18_54, (List.forall_mem_cons.mpr ⟨used_ban_18_72, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good19 : NeighborGood 19 := by
  change ∀ s ∈ [4, 6, 7, 9, 43, 54, 56, 57, 67, 72], NatPairBanned 19 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_4_19.symm, (List.forall_mem_cons.mpr ⟨used_ban_6_19.symm, (List.forall_mem_cons.mpr ⟨used_ban_7_19.symm, (List.forall_mem_cons.mpr ⟨used_ban_9_19.symm, (List.forall_mem_cons.mpr ⟨used_ban_19_43, (List.forall_mem_cons.mpr ⟨used_ban_19_54, (List.forall_mem_cons.mpr ⟨used_ban_19_56, (List.forall_mem_cons.mpr ⟨used_ban_19_57, (List.forall_mem_cons.mpr ⟨used_ban_19_67, (List.forall_mem_cons.mpr ⟨used_ban_19_72, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good20 : NeighborGood 20 := by
  change ∀ s ∈ [12], NatPairBanned 20 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_12_20.symm, List.forall_mem_nil _⟩)
theorem neighbor_good21 : NeighborGood 21 := by
  change ∀ s ∈ [79, 102, 107, 108], NatPairBanned 21 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_21_79, (List.forall_mem_cons.mpr ⟨used_ban_21_102, (List.forall_mem_cons.mpr ⟨used_ban_21_107, (List.forall_mem_cons.mpr ⟨used_ban_21_108, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good22 : NeighborGood 22 := by
  change ∀ s ∈ [15, 34, 38, 39, 94], NatPairBanned 22 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_15_22.symm, (List.forall_mem_cons.mpr ⟨used_ban_22_34, (List.forall_mem_cons.mpr ⟨used_ban_22_38, (List.forall_mem_cons.mpr ⟨used_ban_22_39, (List.forall_mem_cons.mpr ⟨used_ban_22_94, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good23 : NeighborGood 23 := by
  change ∀ s ∈ [], NatPairBanned 23 s
  exact List.forall_mem_nil _
theorem neighbor_good24 : NeighborGood 24 := by
  change ∀ s ∈ [17], NatPairBanned 24 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_17_24.symm, List.forall_mem_nil _⟩)
theorem neighbor_good25 : NeighborGood 25 := by
  change ∀ s ∈ [9, 10, 11, 38, 39, 62, 63, 65, 72, 73, 74, 94], NatPairBanned 25 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_9_25.symm, (List.forall_mem_cons.mpr ⟨used_ban_10_25.symm, (List.forall_mem_cons.mpr ⟨used_ban_11_25.symm, (List.forall_mem_cons.mpr ⟨used_ban_25_38, (List.forall_mem_cons.mpr ⟨used_ban_25_39, (List.forall_mem_cons.mpr ⟨used_ban_25_62, (List.forall_mem_cons.mpr ⟨used_ban_25_63, (List.forall_mem_cons.mpr ⟨used_ban_25_65, (List.forall_mem_cons.mpr ⟨used_ban_25_72, (List.forall_mem_cons.mpr ⟨used_ban_25_73, (List.forall_mem_cons.mpr ⟨used_ban_25_74, (List.forall_mem_cons.mpr ⟨used_ban_25_94, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good26 : NeighborGood 26 := by
  change ∀ s ∈ [0, 1, 9, 10, 11, 12, 13, 14, 17, 36, 54, 58, 59, 60, 61, 62, 63, 68, 71, 72, 73, 74, 82, 86, 134], NatPairBanned 26 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_0_26.symm, (List.forall_mem_cons.mpr ⟨used_ban_1_26.symm, (List.forall_mem_cons.mpr ⟨used_ban_9_26.symm, (List.forall_mem_cons.mpr ⟨used_ban_10_26.symm, (List.forall_mem_cons.mpr ⟨used_ban_11_26.symm, (List.forall_mem_cons.mpr ⟨used_ban_12_26.symm, (List.forall_mem_cons.mpr ⟨used_ban_13_26.symm, (List.forall_mem_cons.mpr ⟨used_ban_14_26.symm, (List.forall_mem_cons.mpr ⟨used_ban_17_26.symm, (List.forall_mem_cons.mpr ⟨used_ban_26_36, (List.forall_mem_cons.mpr ⟨used_ban_26_54, (List.forall_mem_cons.mpr ⟨used_ban_26_58, (List.forall_mem_cons.mpr ⟨used_ban_26_59, (List.forall_mem_cons.mpr ⟨used_ban_26_60, (List.forall_mem_cons.mpr ⟨used_ban_26_61, (List.forall_mem_cons.mpr ⟨used_ban_26_62, (List.forall_mem_cons.mpr ⟨used_ban_26_63, (List.forall_mem_cons.mpr ⟨used_ban_26_68, (List.forall_mem_cons.mpr ⟨used_ban_26_71, (List.forall_mem_cons.mpr ⟨used_ban_26_72, (List.forall_mem_cons.mpr ⟨used_ban_26_73, (List.forall_mem_cons.mpr ⟨used_ban_26_74, (List.forall_mem_cons.mpr ⟨used_ban_26_82, (List.forall_mem_cons.mpr ⟨used_ban_26_86, (List.forall_mem_cons.mpr ⟨used_ban_26_134, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good27 : NeighborGood 27 := by
  change ∀ s ∈ [92, 97, 100, 105], NatPairBanned 27 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_27_92, (List.forall_mem_cons.mpr ⟨used_ban_27_97, (List.forall_mem_cons.mpr ⟨used_ban_27_100, (List.forall_mem_cons.mpr ⟨used_ban_27_105, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good28 : NeighborGood 28 := by
  change ∀ s ∈ [14, 36, 61, 80, 82, 84, 86, 88, 92, 98, 100, 105, 136], NatPairBanned 28 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_14_28.symm, (List.forall_mem_cons.mpr ⟨used_ban_28_36, (List.forall_mem_cons.mpr ⟨used_ban_28_61, (List.forall_mem_cons.mpr ⟨used_ban_28_80, (List.forall_mem_cons.mpr ⟨used_ban_28_82, (List.forall_mem_cons.mpr ⟨used_ban_28_84, (List.forall_mem_cons.mpr ⟨used_ban_28_86, (List.forall_mem_cons.mpr ⟨used_ban_28_88, (List.forall_mem_cons.mpr ⟨used_ban_28_92, (List.forall_mem_cons.mpr ⟨used_ban_28_98, (List.forall_mem_cons.mpr ⟨used_ban_28_100, (List.forall_mem_cons.mpr ⟨used_ban_28_105, (List.forall_mem_cons.mpr ⟨used_ban_28_136, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good29 : NeighborGood 29 := by
  change ∀ s ∈ [14, 34, 36, 37, 92, 96, 98, 99, 102, 104], NatPairBanned 29 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_14_29.symm, (List.forall_mem_cons.mpr ⟨used_ban_29_34, (List.forall_mem_cons.mpr ⟨used_ban_29_36, (List.forall_mem_cons.mpr ⟨used_ban_29_37, (List.forall_mem_cons.mpr ⟨used_ban_29_92, (List.forall_mem_cons.mpr ⟨used_ban_29_96, (List.forall_mem_cons.mpr ⟨used_ban_29_98, (List.forall_mem_cons.mpr ⟨used_ban_29_99, (List.forall_mem_cons.mpr ⟨used_ban_29_102, (List.forall_mem_cons.mpr ⟨used_ban_29_104, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good30 : NeighborGood 30 := by
  change ∀ s ∈ [0, 9, 10, 11, 15, 54, 56, 57, 58, 60, 62, 63, 70, 71, 72, 73, 74, 80, 81, 82, 83, 84, 85, 89], NatPairBanned 30 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_0_30.symm, (List.forall_mem_cons.mpr ⟨used_ban_9_30.symm, (List.forall_mem_cons.mpr ⟨used_ban_10_30.symm, (List.forall_mem_cons.mpr ⟨used_ban_11_30.symm, (List.forall_mem_cons.mpr ⟨used_ban_15_30.symm, (List.forall_mem_cons.mpr ⟨used_ban_30_54, (List.forall_mem_cons.mpr ⟨used_ban_30_56, (List.forall_mem_cons.mpr ⟨used_ban_30_57, (List.forall_mem_cons.mpr ⟨used_ban_30_58, (List.forall_mem_cons.mpr ⟨used_ban_30_60, (List.forall_mem_cons.mpr ⟨used_ban_30_62, (List.forall_mem_cons.mpr ⟨used_ban_30_63, (List.forall_mem_cons.mpr ⟨used_ban_30_70, (List.forall_mem_cons.mpr ⟨used_ban_30_71, (List.forall_mem_cons.mpr ⟨used_ban_30_72, (List.forall_mem_cons.mpr ⟨used_ban_30_73, (List.forall_mem_cons.mpr ⟨used_ban_30_74, (List.forall_mem_cons.mpr ⟨used_ban_30_80, (List.forall_mem_cons.mpr ⟨used_ban_30_81, (List.forall_mem_cons.mpr ⟨used_ban_30_82, (List.forall_mem_cons.mpr ⟨used_ban_30_83, (List.forall_mem_cons.mpr ⟨used_ban_30_84, (List.forall_mem_cons.mpr ⟨used_ban_30_85, (List.forall_mem_cons.mpr ⟨used_ban_30_89, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good31 : NeighborGood 31 := by
  change ∀ s ∈ [12], NatPairBanned 31 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_12_31.symm, List.forall_mem_nil _⟩)
theorem neighbors_range1 : AllRange NeighborGood 16 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good16, (List.forall_mem_cons.mpr ⟨neighbor_good17, (List.forall_mem_cons.mpr ⟨neighbor_good18, (List.forall_mem_cons.mpr ⟨neighbor_good19, (List.forall_mem_cons.mpr ⟨neighbor_good20, (List.forall_mem_cons.mpr ⟨neighbor_good21, (List.forall_mem_cons.mpr ⟨neighbor_good22, (List.forall_mem_cons.mpr ⟨neighbor_good23, (List.forall_mem_cons.mpr ⟨neighbor_good24, (List.forall_mem_cons.mpr ⟨neighbor_good25, (List.forall_mem_cons.mpr ⟨neighbor_good26, (List.forall_mem_cons.mpr ⟨neighbor_good27, (List.forall_mem_cons.mpr ⟨neighbor_good28, (List.forall_mem_cons.mpr ⟨neighbor_good29, (List.forall_mem_cons.mpr ⟨neighbor_good30, (List.forall_mem_cons.mpr ⟨neighbor_good31, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range1
