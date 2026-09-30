import ElevenSquare.Tasks.T06.BranchDigit00
import ElevenSquare.Tasks.T06.BranchDigit01
import ElevenSquare.Tasks.T06.BranchDigit02
import ElevenSquare.Tasks.T06.BranchDigit03
import ElevenSquare.Tasks.T06.BranchDigit04
import ElevenSquare.Tasks.T06.BranchDigit05
import ElevenSquare.Tasks.T06.BranchDigit06
import ElevenSquare.Tasks.T06.BranchDigit07
import ElevenSquare.Tasks.T06.BranchDigit08
import ElevenSquare.Tasks.T06.BranchDigit09
import ElevenSquare.Tasks.T06.BranchDigit10
import ElevenSquare.Tasks.T06.BranchDigit11
import ElevenSquare.Tasks.T06.BranchDigit12
import ElevenSquare.Tasks.T06.BranchDigit13
import ElevenSquare.Tasks.T06.BranchDigit14
import ElevenSquare.Tasks.T06.BranchDigit15

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem digitSelection_spec (a b : Fin 2) (c : Fin 4) :
    ∀ d e f g h : Fin 2, ∀ p : Fin 14,
      rawSelections (digitIndex a b c d e f g h) p = digitChoices a b c d e f g h p := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exact digit_selection_00
  · exact digit_selection_01
  · exact digit_selection_02
  · exact digit_selection_03
  · exact digit_selection_04
  · exact digit_selection_05
  · exact digit_selection_06
  · exact digit_selection_07
  · exact digit_selection_08
  · exact digit_selection_09
  · exact digit_selection_10
  · exact digit_selection_11
  · exact digit_selection_12
  · exact digit_selection_13
  · exact digit_selection_14
  · exact digit_selection_15

theorem choose_two (x a b : Fin 112) (hx : x ∈ [a, b]) :
    ∃ i : Fin 2, (![a, b] : Fin 2 → Fin 112) i = x := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem choose_four (x a b c d : Fin 112) (hx : x ∈ [a, b, c, d]) :
    ∃ i : Fin 4, (![a, b, c, d] : Fin 4 → Fin 112) i = x := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

theorem rawSelections_complete (choose : FeatureSelection) :
    ∃ r : Fin 512, ∀ p : Fin 14, rawSelections r p = (choose p).val := by
  have h0 : (choose 0).val = 7 :=
    List.mem_singleton.mp (show (choose 0).val ∈ [7] from (choose 0).property)
  have h1 : (choose 1).val = 12 :=
    List.mem_singleton.mp (show (choose 1).val ∈ [12] from (choose 1).property)
  have h2 : (choose 2).val = 22 :=
    List.mem_singleton.mp (show (choose 2).val ∈ [22] from (choose 2).property)
  have h3 : (choose 3).val = 29 :=
    List.mem_singleton.mp (show (choose 3).val ∈ [29] from (choose 3).property)
  have h7 : (choose 7).val = 61 :=
    List.mem_singleton.mp (show (choose 7).val ∈ [61] from (choose 7).property)
  have h8 : (choose 8).val = 69 :=
    List.mem_singleton.mp (show (choose 8).val ∈ [69] from (choose 8).property)
  obtain ⟨a, h4⟩ := choose_two (choose 4).val 35 39
    (show (choose 4).val ∈ [35, 39] from (choose 4).property)
  obtain ⟨b, h5⟩ := choose_two (choose 5).val 41 45
    (show (choose 5).val ∈ [41, 45] from (choose 5).property)
  obtain ⟨c, h6⟩ := choose_four (choose 6).val 49 50 53 54
    (show (choose 6).val ∈ [49, 50, 53, 54] from (choose 6).property)
  obtain ⟨d, h9⟩ := choose_two (choose 9).val 73 77
    (show (choose 9).val ∈ [73, 77] from (choose 9).property)
  obtain ⟨e, h10⟩ := choose_two (choose 10).val 83 87
    (show (choose 10).val ∈ [83, 87] from (choose 10).property)
  obtain ⟨f, h11⟩ := choose_two (choose 11).val 91 95
    (show (choose 11).val ∈ [91, 95] from (choose 11).property)
  obtain ⟨g, h12⟩ := choose_two (choose 12).val 97 101
    (show (choose 12).val ∈ [97, 101] from (choose 12).property)
  obtain ⟨h, h13⟩ := choose_two (choose 13).val 107 111
    (show (choose 13).val ∈ [107, 111] from (choose 13).property)
  refine ⟨digitIndex a b c d e f g h, ?_⟩
  intro p
  rw [digitSelection_spec]
  fin_cases p
  · exact h0.symm
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm
  · exact h4
  · exact h5
  · exact h6
  · exact h7.symm
  · exact h8.symm
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13

theorem rawSelectionBranch_surjective : Function.Surjective rawSelectionBranch := by
  intro b
  fin_cases b
  · exact ⟨12, rfl⟩
  · exact ⟨76, rfl⟩
  · exact ⟨108, rfl⟩
  · exact ⟨44, rfl⟩
  · exact ⟨13, rfl⟩
  · exact ⟨77, rfl⟩
  · exact ⟨109, rfl⟩
  · exact ⟨45, rfl⟩
  · exact ⟨14, rfl⟩
  · exact ⟨78, rfl⟩
  · exact ⟨110, rfl⟩
  · exact ⟨46, rfl⟩
  · exact ⟨15, rfl⟩
  · exact ⟨79, rfl⟩
  · exact ⟨111, rfl⟩
  · exact ⟨47, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨72, rfl⟩
  · exact ⟨104, rfl⟩
  · exact ⟨40, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨73, rfl⟩
  · exact ⟨105, rfl⟩
  · exact ⟨41, rfl⟩
  · exact ⟨10, rfl⟩
  · exact ⟨74, rfl⟩
  · exact ⟨106, rfl⟩
  · exact ⟨42, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨75, rfl⟩
  · exact ⟨107, rfl⟩
  · exact ⟨43, rfl⟩
  · exact ⟨28, rfl⟩
  · exact ⟨92, rfl⟩
  · exact ⟨124, rfl⟩
  · exact ⟨60, rfl⟩
  · exact ⟨29, rfl⟩
  · exact ⟨93, rfl⟩
  · exact ⟨125, rfl⟩
  · exact ⟨61, rfl⟩
  · exact ⟨30, rfl⟩
  · exact ⟨94, rfl⟩
  · exact ⟨126, rfl⟩
  · exact ⟨62, rfl⟩
  · exact ⟨31, rfl⟩
  · exact ⟨95, rfl⟩
  · exact ⟨127, rfl⟩
  · exact ⟨63, rfl⟩
  · exact ⟨24, rfl⟩
  · exact ⟨88, rfl⟩
  · exact ⟨120, rfl⟩
  · exact ⟨56, rfl⟩
  · exact ⟨25, rfl⟩
  · exact ⟨89, rfl⟩
  · exact ⟨121, rfl⟩
  · exact ⟨57, rfl⟩
  · exact ⟨26, rfl⟩
  · exact ⟨90, rfl⟩
  · exact ⟨122, rfl⟩
  · exact ⟨58, rfl⟩
  · exact ⟨27, rfl⟩
  · exact ⟨91, rfl⟩
  · exact ⟨123, rfl⟩
  · exact ⟨59, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨68, rfl⟩
  · exact ⟨100, rfl⟩
  · exact ⟨36, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨69, rfl⟩
  · exact ⟨101, rfl⟩
  · exact ⟨37, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨70, rfl⟩
  · exact ⟨102, rfl⟩
  · exact ⟨38, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨71, rfl⟩
  · exact ⟨103, rfl⟩
  · exact ⟨39, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨64, rfl⟩
  · exact ⟨96, rfl⟩
  · exact ⟨32, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨65, rfl⟩
  · exact ⟨97, rfl⟩
  · exact ⟨33, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨66, rfl⟩
  · exact ⟨98, rfl⟩
  · exact ⟨34, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨67, rfl⟩
  · exact ⟨99, rfl⟩
  · exact ⟨35, rfl⟩
  · exact ⟨20, rfl⟩
  · exact ⟨84, rfl⟩
  · exact ⟨116, rfl⟩
  · exact ⟨52, rfl⟩
  · exact ⟨21, rfl⟩
  · exact ⟨85, rfl⟩
  · exact ⟨117, rfl⟩
  · exact ⟨53, rfl⟩
  · exact ⟨22, rfl⟩
  · exact ⟨86, rfl⟩
  · exact ⟨118, rfl⟩
  · exact ⟨54, rfl⟩
  · exact ⟨23, rfl⟩
  · exact ⟨87, rfl⟩
  · exact ⟨119, rfl⟩
  · exact ⟨55, rfl⟩
  · exact ⟨16, rfl⟩
  · exact ⟨80, rfl⟩
  · exact ⟨112, rfl⟩
  · exact ⟨48, rfl⟩
  · exact ⟨17, rfl⟩
  · exact ⟨81, rfl⟩
  · exact ⟨113, rfl⟩
  · exact ⟨49, rfl⟩
  · exact ⟨18, rfl⟩
  · exact ⟨82, rfl⟩
  · exact ⟨114, rfl⟩
  · exact ⟨50, rfl⟩
  · exact ⟨19, rfl⟩
  · exact ⟨83, rfl⟩
  · exact ⟨115, rfl⟩
  · exact ⟨51, rfl⟩

end
end ElevenSquare.Tasks.T06
