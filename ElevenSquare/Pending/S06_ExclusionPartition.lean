import ElevenSquare.Pending.S06_ExclusionPartitionChunks0
import ElevenSquare.Pending.S06_ExclusionPartitionChunks1
import ElevenSquare.Pending.S06_ExclusionPartitionChunks2
import ElevenSquare.Pending.S06_ExclusionPartitionChunks3
import ElevenSquare.Pending.S06_ExclusionPartitionChunks4
import ElevenSquare.Pending.S06_ExclusionPartitionChunks5
import ElevenSquare.Pending.S06_ExclusionPartitionChunks6
import ElevenSquare.Pending.S06_ExclusionPartitionChunks7
import ElevenSquare.Pending.S06_ExclusionSmallLists
import ElevenSquare.Pending.FinitePartition
namespace ElevenSquare.Pending.ExclusionCounts
theorem baseline_good_all : BaselineGood baselineArray := by
  unfold baselineArray
  exact ((((((((((((((((((((((((((((((baseline_good0.append baseline_good1).append baseline_good2).append baseline_good3).append baseline_good4).append baseline_good5).append baseline_good6).append baseline_good7).append baseline_good8).append baseline_good9).append baseline_good10).append baseline_good11).append baseline_good12).append baseline_good13).append baseline_good14).append baseline_good15).append baseline_good16).append baseline_good17).append baseline_good18).append baseline_good19).append baseline_good20).append baseline_good21).append baseline_good22).append baseline_good23).append baseline_good24).append baseline_good25).append baseline_good26).append baseline_good27).append baseline_good28).append baseline_good29).append baseline_good30)
theorem list_subset_range (xs : List ℕ) (n : ℕ) (h : ∀ x ∈ xs, x < n) :
    xs.toFinset ⊆ Finset.range n := by
  intro x hx
  exact Finset.mem_range.mpr (h x (List.mem_toFinset.mp hx))
end ElevenSquare.Pending.ExclusionCounts

namespace ElevenSquare.Pending
open ExclusionCounts

theorem exclusion_inventory :
    baselineIndices.card = 1931 ∧ priorIndices.card = 76 ∧ returnedIndices.card = 173 ∧
    Disjoint baselineIndices priorIndices ∧ Disjoint baselineIndices returnedIndices ∧
    Disjoint priorIndices returnedIndices ∧
    baselineIndices ∪ priorIndices ∪ returnedIndices = Finset.range 2184 \ candidateIndices := by
  have hbp : Disjoint baselineIndices priorIndices :=
    List.disjoint_toFinset_iff_disjoint.mpr baseline_good_all.2.1
  have hbr : Disjoint baselineIndices returnedIndices :=
    List.disjoint_toFinset_iff_disjoint.mpr baseline_good_all.2.2.1
  have hbc : Disjoint baselineIndices candidateIndices :=
    List.disjoint_toFinset_iff_disjoint.mpr baseline_good_all.2.2.2
  have hpr : Disjoint priorIndices returnedIndices :=
    List.disjoint_toFinset_iff_disjoint.mpr prior_returned_disjoint
  have hpc : Disjoint priorIndices candidateIndices :=
    List.disjoint_toFinset_iff_disjoint.mpr prior_candidate_disjoint
  have hrc : Disjoint returnedIndices candidateIndices :=
    List.disjoint_toFinset_iff_disjoint.mpr returned_candidate_disjoint
  refine ⟨baseline_card, prior_card, returned_card, hbp, hbr, hpr, ?_⟩
  exact finite_partition_of_cards _ _ _ _ baseline_card prior_card returned_card candidate_card
    hbp hbr hbc hpr hpc hrc
    (list_subset_range _ _ baseline_good_all.1) (list_subset_range _ _ prior_bound)
    (list_subset_range _ _ returned_bound) (list_subset_range _ _ candidate_bound)
end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.exclusion_inventory
