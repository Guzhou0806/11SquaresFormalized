import ElevenSquare.Pending.S07_EncodedSemanticSupport
import ElevenSquare.Pending.S07_SelectedBanFacts0
import ElevenSquare.Pending.S07_SelectedBanFacts1
import ElevenSquare.Pending.S07_SelectedBanFacts2
namespace ElevenSquare.Pending.EncodedSearch
theorem neighbor_good0 : NeighborGood 0 := by
  change ∀ s ∈ [26, 30, 64, 66, 67, 68], NatPairBanned 0 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_0_26, (List.forall_mem_cons.mpr ⟨used_ban_0_30, (List.forall_mem_cons.mpr ⟨used_ban_0_64, (List.forall_mem_cons.mpr ⟨used_ban_0_66, (List.forall_mem_cons.mpr ⟨used_ban_0_67, (List.forall_mem_cons.mpr ⟨used_ban_0_68, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good1 : NeighborGood 1 := by
  change ∀ s ∈ [14, 26, 65, 67, 68, 69, 70, 131], NatPairBanned 1 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_1_14, (List.forall_mem_cons.mpr ⟨used_ban_1_26, (List.forall_mem_cons.mpr ⟨used_ban_1_65, (List.forall_mem_cons.mpr ⟨used_ban_1_67, (List.forall_mem_cons.mpr ⟨used_ban_1_68, (List.forall_mem_cons.mpr ⟨used_ban_1_69, (List.forall_mem_cons.mpr ⟨used_ban_1_70, (List.forall_mem_cons.mpr ⟨used_ban_1_131, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good2 : NeighborGood 2 := by
  change ∀ s ∈ [], NatPairBanned 2 s
  exact List.forall_mem_nil _
theorem neighbor_good3 : NeighborGood 3 := by
  change ∀ s ∈ [17, 54], NatPairBanned 3 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_3_17, (List.forall_mem_cons.mpr ⟨used_ban_3_54, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good4 : NeighborGood 4 := by
  change ∀ s ∈ [19, 56, 128, 144], NatPairBanned 4 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_4_19, (List.forall_mem_cons.mpr ⟨used_ban_4_56, (List.forall_mem_cons.mpr ⟨used_ban_4_128, (List.forall_mem_cons.mpr ⟨used_ban_4_144, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good5 : NeighborGood 5 := by
  change ∀ s ∈ [41, 48, 52, 53, 144], NatPairBanned 5 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_5_41, (List.forall_mem_cons.mpr ⟨used_ban_5_48, (List.forall_mem_cons.mpr ⟨used_ban_5_52, (List.forall_mem_cons.mpr ⟨used_ban_5_53, (List.forall_mem_cons.mpr ⟨used_ban_5_144, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good6 : NeighborGood 6 := by
  change ∀ s ∈ [15, 18, 19, 70, 128], NatPairBanned 6 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_6_15, (List.forall_mem_cons.mpr ⟨used_ban_6_18, (List.forall_mem_cons.mpr ⟨used_ban_6_19, (List.forall_mem_cons.mpr ⟨used_ban_6_70, (List.forall_mem_cons.mpr ⟨used_ban_6_128, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good7 : NeighborGood 7 := by
  change ∀ s ∈ [19, 54], NatPairBanned 7 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_7_19, (List.forall_mem_cons.mpr ⟨used_ban_7_54, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good8 : NeighborGood 8 := by
  change ∀ s ∈ [54], NatPairBanned 8 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_8_54, List.forall_mem_nil _⟩)
theorem neighbor_good9 : NeighborGood 9 := by
  change ∀ s ∈ [12, 15, 16, 17, 18, 19, 25, 26, 30, 65, 70, 128], NatPairBanned 9 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_9_12, (List.forall_mem_cons.mpr ⟨used_ban_9_15, (List.forall_mem_cons.mpr ⟨used_ban_9_16, (List.forall_mem_cons.mpr ⟨used_ban_9_17, (List.forall_mem_cons.mpr ⟨used_ban_9_18, (List.forall_mem_cons.mpr ⟨used_ban_9_19, (List.forall_mem_cons.mpr ⟨used_ban_9_25, (List.forall_mem_cons.mpr ⟨used_ban_9_26, (List.forall_mem_cons.mpr ⟨used_ban_9_30, (List.forall_mem_cons.mpr ⟨used_ban_9_65, (List.forall_mem_cons.mpr ⟨used_ban_9_70, (List.forall_mem_cons.mpr ⟨used_ban_9_128, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good10 : NeighborGood 10 := by
  change ∀ s ∈ [17, 25, 26, 30], NatPairBanned 10 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_10_17, (List.forall_mem_cons.mpr ⟨used_ban_10_25, (List.forall_mem_cons.mpr ⟨used_ban_10_26, (List.forall_mem_cons.mpr ⟨used_ban_10_30, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good11 : NeighborGood 11 := by
  change ∀ s ∈ [17, 25, 26, 30], NatPairBanned 11 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_11_17, (List.forall_mem_cons.mpr ⟨used_ban_11_25, (List.forall_mem_cons.mpr ⟨used_ban_11_26, (List.forall_mem_cons.mpr ⟨used_ban_11_30, List.forall_mem_nil _⟩)⟩)⟩)⟩)
theorem neighbor_good12 : NeighborGood 12 := by
  change ∀ s ∈ [9, 20, 26, 31, 32, 54, 56, 57, 67, 72], NatPairBanned 12 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_9_12.symm, (List.forall_mem_cons.mpr ⟨used_ban_12_20, (List.forall_mem_cons.mpr ⟨used_ban_12_26, (List.forall_mem_cons.mpr ⟨used_ban_12_31, (List.forall_mem_cons.mpr ⟨used_ban_12_32, (List.forall_mem_cons.mpr ⟨used_ban_12_54, (List.forall_mem_cons.mpr ⟨used_ban_12_56, (List.forall_mem_cons.mpr ⟨used_ban_12_57, (List.forall_mem_cons.mpr ⟨used_ban_12_67, (List.forall_mem_cons.mpr ⟨used_ban_12_72, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good13 : NeighborGood 13 := by
  change ∀ s ∈ [26, 57], NatPairBanned 13 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_13_26, (List.forall_mem_cons.mpr ⟨used_ban_13_57, List.forall_mem_nil _⟩)⟩)
theorem neighbor_good14 : NeighborGood 14 := by
  change ∀ s ∈ [1, 26, 28, 29, 55, 57, 59, 64, 94, 107], NatPairBanned 14 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_1_14.symm, (List.forall_mem_cons.mpr ⟨used_ban_14_26, (List.forall_mem_cons.mpr ⟨used_ban_14_28, (List.forall_mem_cons.mpr ⟨used_ban_14_29, (List.forall_mem_cons.mpr ⟨used_ban_14_55, (List.forall_mem_cons.mpr ⟨used_ban_14_57, (List.forall_mem_cons.mpr ⟨used_ban_14_59, (List.forall_mem_cons.mpr ⟨used_ban_14_64, (List.forall_mem_cons.mpr ⟨used_ban_14_94, (List.forall_mem_cons.mpr ⟨used_ban_14_107, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbor_good15 : NeighborGood 15 := by
  change ∀ s ∈ [6, 9, 22, 30, 64, 66, 67, 71, 72], NatPairBanned 15 s
  exact (List.forall_mem_cons.mpr ⟨used_ban_6_15.symm, (List.forall_mem_cons.mpr ⟨used_ban_9_15.symm, (List.forall_mem_cons.mpr ⟨used_ban_15_22, (List.forall_mem_cons.mpr ⟨used_ban_15_30, (List.forall_mem_cons.mpr ⟨used_ban_15_64, (List.forall_mem_cons.mpr ⟨used_ban_15_66, (List.forall_mem_cons.mpr ⟨used_ban_15_67, (List.forall_mem_cons.mpr ⟨used_ban_15_71, (List.forall_mem_cons.mpr ⟨used_ban_15_72, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem neighbors_range0 : AllRange NeighborGood 0 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], NeighborGood r
  exact (List.forall_mem_cons.mpr ⟨neighbor_good0, (List.forall_mem_cons.mpr ⟨neighbor_good1, (List.forall_mem_cons.mpr ⟨neighbor_good2, (List.forall_mem_cons.mpr ⟨neighbor_good3, (List.forall_mem_cons.mpr ⟨neighbor_good4, (List.forall_mem_cons.mpr ⟨neighbor_good5, (List.forall_mem_cons.mpr ⟨neighbor_good6, (List.forall_mem_cons.mpr ⟨neighbor_good7, (List.forall_mem_cons.mpr ⟨neighbor_good8, (List.forall_mem_cons.mpr ⟨neighbor_good9, (List.forall_mem_cons.mpr ⟨neighbor_good10, (List.forall_mem_cons.mpr ⟨neighbor_good11, (List.forall_mem_cons.mpr ⟨neighbor_good12, (List.forall_mem_cons.mpr ⟨neighbor_good13, (List.forall_mem_cons.mpr ⟨neighbor_good14, (List.forall_mem_cons.mpr ⟨neighbor_good15, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_range0
