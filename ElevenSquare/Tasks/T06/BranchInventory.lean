import ElevenSquare.Tasks.T06.DataFeatures
import ElevenSquare.Pending.S08_FeatureBranches
import ElevenSquare.Pending.S08_GapFeatures
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Fin.Basic

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

deriving instance DecidableEq for SeparationFeature
deriving instance DecidableEq for Gap

theorem contactPairs_distinct (p : Fin 14) :
    (contactPairs p).1 ≠ (contactPairs p).2 := by
  fin_cases p <;> decide

theorem feature_inventory_partition :
    ∀ f : Fin 112,
      (∃ a : Fin 24, activeFeatureIds a = f) ∨
      (∃ u : Fin 88, unavailableFeatureIds u = f) := by
  intro f
  fin_cases f
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inr ⟨1, rfl⟩
  · exact Or.inr ⟨2, rfl⟩
  · exact Or.inr ⟨3, rfl⟩
  · exact Or.inr ⟨4, rfl⟩
  · exact Or.inr ⟨5, rfl⟩
  · exact Or.inr ⟨6, rfl⟩
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inr ⟨7, rfl⟩
  · exact Or.inr ⟨8, rfl⟩
  · exact Or.inr ⟨9, rfl⟩
  · exact Or.inr ⟨10, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inr ⟨11, rfl⟩
  · exact Or.inr ⟨12, rfl⟩
  · exact Or.inr ⟨13, rfl⟩
  · exact Or.inr ⟨14, rfl⟩
  · exact Or.inr ⟨15, rfl⟩
  · exact Or.inr ⟨16, rfl⟩
  · exact Or.inr ⟨17, rfl⟩
  · exact Or.inr ⟨18, rfl⟩
  · exact Or.inr ⟨19, rfl⟩
  · exact Or.inl ⟨2, rfl⟩
  · exact Or.inr ⟨20, rfl⟩
  · exact Or.inr ⟨21, rfl⟩
  · exact Or.inr ⟨22, rfl⟩
  · exact Or.inr ⟨23, rfl⟩
  · exact Or.inr ⟨24, rfl⟩
  · exact Or.inr ⟨25, rfl⟩
  · exact Or.inl ⟨3, rfl⟩
  · exact Or.inr ⟨26, rfl⟩
  · exact Or.inr ⟨27, rfl⟩
  · exact Or.inr ⟨28, rfl⟩
  · exact Or.inr ⟨29, rfl⟩
  · exact Or.inr ⟨30, rfl⟩
  · exact Or.inl ⟨4, rfl⟩
  · exact Or.inr ⟨31, rfl⟩
  · exact Or.inr ⟨32, rfl⟩
  · exact Or.inr ⟨33, rfl⟩
  · exact Or.inl ⟨5, rfl⟩
  · exact Or.inr ⟨34, rfl⟩
  · exact Or.inl ⟨6, rfl⟩
  · exact Or.inr ⟨35, rfl⟩
  · exact Or.inr ⟨36, rfl⟩
  · exact Or.inr ⟨37, rfl⟩
  · exact Or.inl ⟨7, rfl⟩
  · exact Or.inr ⟨38, rfl⟩
  · exact Or.inr ⟨39, rfl⟩
  · exact Or.inr ⟨40, rfl⟩
  · exact Or.inl ⟨8, rfl⟩
  · exact Or.inl ⟨9, rfl⟩
  · exact Or.inr ⟨41, rfl⟩
  · exact Or.inr ⟨42, rfl⟩
  · exact Or.inl ⟨10, rfl⟩
  · exact Or.inl ⟨11, rfl⟩
  · exact Or.inr ⟨43, rfl⟩
  · exact Or.inr ⟨44, rfl⟩
  · exact Or.inr ⟨45, rfl⟩
  · exact Or.inr ⟨46, rfl⟩
  · exact Or.inr ⟨47, rfl⟩
  · exact Or.inr ⟨48, rfl⟩
  · exact Or.inl ⟨12, rfl⟩
  · exact Or.inr ⟨49, rfl⟩
  · exact Or.inr ⟨50, rfl⟩
  · exact Or.inr ⟨51, rfl⟩
  · exact Or.inr ⟨52, rfl⟩
  · exact Or.inr ⟨53, rfl⟩
  · exact Or.inr ⟨54, rfl⟩
  · exact Or.inr ⟨55, rfl⟩
  · exact Or.inl ⟨13, rfl⟩
  · exact Or.inr ⟨56, rfl⟩
  · exact Or.inr ⟨57, rfl⟩
  · exact Or.inr ⟨58, rfl⟩
  · exact Or.inl ⟨14, rfl⟩
  · exact Or.inr ⟨59, rfl⟩
  · exact Or.inr ⟨60, rfl⟩
  · exact Or.inr ⟨61, rfl⟩
  · exact Or.inl ⟨15, rfl⟩
  · exact Or.inr ⟨62, rfl⟩
  · exact Or.inr ⟨63, rfl⟩
  · exact Or.inr ⟨64, rfl⟩
  · exact Or.inr ⟨65, rfl⟩
  · exact Or.inr ⟨66, rfl⟩
  · exact Or.inl ⟨16, rfl⟩
  · exact Or.inr ⟨67, rfl⟩
  · exact Or.inr ⟨68, rfl⟩
  · exact Or.inr ⟨69, rfl⟩
  · exact Or.inl ⟨17, rfl⟩
  · exact Or.inr ⟨70, rfl⟩
  · exact Or.inr ⟨71, rfl⟩
  · exact Or.inr ⟨72, rfl⟩
  · exact Or.inl ⟨18, rfl⟩
  · exact Or.inr ⟨73, rfl⟩
  · exact Or.inr ⟨74, rfl⟩
  · exact Or.inr ⟨75, rfl⟩
  · exact Or.inl ⟨19, rfl⟩
  · exact Or.inr ⟨76, rfl⟩
  · exact Or.inl ⟨20, rfl⟩
  · exact Or.inr ⟨77, rfl⟩
  · exact Or.inr ⟨78, rfl⟩
  · exact Or.inr ⟨79, rfl⟩
  · exact Or.inl ⟨21, rfl⟩
  · exact Or.inr ⟨80, rfl⟩
  · exact Or.inr ⟨81, rfl⟩
  · exact Or.inr ⟨82, rfl⟩
  · exact Or.inr ⟨83, rfl⟩
  · exact Or.inr ⟨84, rfl⟩
  · exact Or.inl ⟨22, rfl⟩
  · exact Or.inr ⟨85, rfl⟩
  · exact Or.inr ⟨86, rfl⟩
  · exact Or.inr ⟨87, rfl⟩
  · exact Or.inl ⟨23, rfl⟩

def activeIdList : List (Fin 112) := [7, 12, 22, 29, 35, 39, 41, 45, 49, 50, 53, 54, 61, 69, 73, 77, 83, 87, 91, 95, 97, 101, 107, 111]

theorem active_mem_list (a : Fin 24) : activeFeatureIds a ∈ activeIdList := by
  fin_cases a <;> decide

theorem unavailable_not_mem_list (u : Fin 88) : unavailableFeatureIds u ∉ activeIdList := by
  fin_cases u <;> decide

theorem feature_inventory_disjoint :
    ∀ a : Fin 24, ∀ u : Fin 88, activeFeatureIds a ≠ unavailableFeatureIds u := by
  intro a u h
  have hm := active_mem_list a
  rw [h] at hm
  exact unavailable_not_mem_list u hm

theorem feature_inventory_nodup :
    Function.Injective activeFeatureIds ∧ Function.Injective unavailableFeatureIds := by
  constructor
  · apply StrictMono.injective
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · apply StrictMono.injective
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide

theorem feature_inventory_complete (p : Fin 14) (f : SeparationFeature)
    (hpair :
      (f.owner = (contactPairs p).1 ∧ f.other = (contactPairs p).2) ∨
      (f.owner = (contactPairs p).2 ∧ f.other = (contactPairs p).1)) :
    ∃ id : Fin 112, id.val / 8 = p.val ∧ allFeatures id = f := by
  rcases f with ⟨owner, other, distinct, perpendicular, reverse⟩
  fin_cases p
  · change ((owner = 0 ∧ other = 6) ∨ (owner = 6 ∧ other = 0)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨3, rfl, rfl⟩
      · exact ⟨2, rfl, rfl⟩
      · exact ⟨0, rfl, rfl⟩
      · exact ⟨1, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨6, rfl, rfl⟩
      · exact ⟨7, rfl, rfl⟩
      · exact ⟨5, rfl, rfl⟩
      · exact ⟨4, rfl, rfl⟩
  · change ((owner = 1 ∧ other = 9) ∨ (owner = 9 ∧ other = 1)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨11, rfl, rfl⟩
      · exact ⟨10, rfl, rfl⟩
      · exact ⟨8, rfl, rfl⟩
      · exact ⟨9, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨14, rfl, rfl⟩
      · exact ⟨15, rfl, rfl⟩
      · exact ⟨13, rfl, rfl⟩
      · exact ⟨12, rfl, rfl⟩
  · change ((owner = 2 ∧ other = 8) ∨ (owner = 8 ∧ other = 2)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨19, rfl, rfl⟩
      · exact ⟨18, rfl, rfl⟩
      · exact ⟨16, rfl, rfl⟩
      · exact ⟨17, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨22, rfl, rfl⟩
      · exact ⟨23, rfl, rfl⟩
      · exact ⟨21, rfl, rfl⟩
      · exact ⟨20, rfl, rfl⟩
  · change ((owner = 2 ∧ other = 10) ∨ (owner = 10 ∧ other = 2)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨27, rfl, rfl⟩
      · exact ⟨26, rfl, rfl⟩
      · exact ⟨24, rfl, rfl⟩
      · exact ⟨25, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨30, rfl, rfl⟩
      · exact ⟨31, rfl, rfl⟩
      · exact ⟨29, rfl, rfl⟩
      · exact ⟨28, rfl, rfl⟩
  · change ((owner = 3 ∧ other = 4) ∨ (owner = 4 ∧ other = 3)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨35, rfl, rfl⟩
      · exact ⟨34, rfl, rfl⟩
      · exact ⟨32, rfl, rfl⟩
      · exact ⟨33, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨38, rfl, rfl⟩
      · exact ⟨39, rfl, rfl⟩
      · exact ⟨37, rfl, rfl⟩
      · exact ⟨36, rfl, rfl⟩
  · change ((owner = 3 ∧ other = 5) ∨ (owner = 5 ∧ other = 3)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨43, rfl, rfl⟩
      · exact ⟨42, rfl, rfl⟩
      · exact ⟨40, rfl, rfl⟩
      · exact ⟨41, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨46, rfl, rfl⟩
      · exact ⟨47, rfl, rfl⟩
      · exact ⟨45, rfl, rfl⟩
      · exact ⟨44, rfl, rfl⟩
  · change ((owner = 4 ∧ other = 5) ∨ (owner = 5 ∧ other = 4)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨51, rfl, rfl⟩
      · exact ⟨50, rfl, rfl⟩
      · exact ⟨48, rfl, rfl⟩
      · exact ⟨49, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨54, rfl, rfl⟩
      · exact ⟨55, rfl, rfl⟩
      · exact ⟨53, rfl, rfl⟩
      · exact ⟨52, rfl, rfl⟩
  · change ((owner = 4 ∧ other = 8) ∨ (owner = 8 ∧ other = 4)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨59, rfl, rfl⟩
      · exact ⟨58, rfl, rfl⟩
      · exact ⟨56, rfl, rfl⟩
      · exact ⟨57, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨62, rfl, rfl⟩
      · exact ⟨63, rfl, rfl⟩
      · exact ⟨61, rfl, rfl⟩
      · exact ⟨60, rfl, rfl⟩
  · change ((owner = 5 ∧ other = 6) ∨ (owner = 6 ∧ other = 5)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨67, rfl, rfl⟩
      · exact ⟨66, rfl, rfl⟩
      · exact ⟨64, rfl, rfl⟩
      · exact ⟨65, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨70, rfl, rfl⟩
      · exact ⟨71, rfl, rfl⟩
      · exact ⟨69, rfl, rfl⟩
      · exact ⟨68, rfl, rfl⟩
  · change ((owner = 6 ∧ other = 7) ∨ (owner = 7 ∧ other = 6)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨75, rfl, rfl⟩
      · exact ⟨74, rfl, rfl⟩
      · exact ⟨72, rfl, rfl⟩
      · exact ⟨73, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨78, rfl, rfl⟩
      · exact ⟨79, rfl, rfl⟩
      · exact ⟨77, rfl, rfl⟩
      · exact ⟨76, rfl, rfl⟩
  · change ((owner = 6 ∧ other = 8) ∨ (owner = 8 ∧ other = 6)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨83, rfl, rfl⟩
      · exact ⟨82, rfl, rfl⟩
      · exact ⟨80, rfl, rfl⟩
      · exact ⟨81, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨86, rfl, rfl⟩
      · exact ⟨87, rfl, rfl⟩
      · exact ⟨85, rfl, rfl⟩
      · exact ⟨84, rfl, rfl⟩
  · change ((owner = 7 ∧ other = 9) ∨ (owner = 9 ∧ other = 7)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨91, rfl, rfl⟩
      · exact ⟨90, rfl, rfl⟩
      · exact ⟨88, rfl, rfl⟩
      · exact ⟨89, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨94, rfl, rfl⟩
      · exact ⟨95, rfl, rfl⟩
      · exact ⟨93, rfl, rfl⟩
      · exact ⟨92, rfl, rfl⟩
  · change ((owner = 8 ∧ other = 9) ∨ (owner = 9 ∧ other = 8)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨99, rfl, rfl⟩
      · exact ⟨98, rfl, rfl⟩
      · exact ⟨96, rfl, rfl⟩
      · exact ⟨97, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨102, rfl, rfl⟩
      · exact ⟨103, rfl, rfl⟩
      · exact ⟨101, rfl, rfl⟩
      · exact ⟨100, rfl, rfl⟩
  · change ((owner = 9 ∧ other = 10) ∨ (owner = 10 ∧ other = 9)) at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨107, rfl, rfl⟩
      · exact ⟨106, rfl, rfl⟩
      · exact ⟨104, rfl, rfl⟩
      · exact ⟨105, rfl, rfl⟩
    · cases perpendicular <;> cases reverse
      · exact ⟨110, rfl, rfl⟩
      · exact ⟨111, rfl, rfl⟩
      · exact ⟨109, rfl, rfl⟩
      · exact ⟨108, rfl, rfl⟩

theorem active_feature_allowed :
    ∀ a : Fin 24, ∀ p : Fin 14, (activeFeatureIds a).val / 8 = p.val →
      activeFeatureIds a ∈ allowedFeatureIds p := by
  intro a
  fin_cases a <;> decide

theorem allowed_or_unavailable :
    ∀ p : Fin 14, ∀ id : Fin 112, id.val / 8 = p.val →
      id ∈ allowedFeatureIds p ∨
        ∃ u : Fin 88, unavailableFeatureIds u = id := by
  intro p id hid
  rcases feature_inventory_partition id with ⟨a, ha⟩ | hu
  · left
    rw [← ha] at hid ⊢
    exact active_feature_allowed a p hid
  · exact Or.inr hu

end
end ElevenSquare.Tasks.T06
