import ElevenSquare.Pending.S07_Data
import ElevenSquare.Pending.OrderedData
namespace ElevenSquare.Pending.EncodedSearch
open OrderedData
def NatPairBanned (r s : ℕ) : Prop := (r,s) ∈ bannedPairs ∨ (s,r) ∈ bannedPairs
theorem NatPairBanned.symm {r s : ℕ} (h : NatPairBanned r s) : NatPairBanned s r := Or.symm h
theorem listed_pair_banned (r s : ℕ) (h : (r,s) ∈ bannedPairArray.toList) : NatPairBanned r s := Or.inl (List.mem_toFinset.mpr h)
theorem ban_chunk_mem0 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk0.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))))))))))))))))))))
theorem ban_chunk_mem1 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk1.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))))))))))))))))
theorem ban_chunk_mem2 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk2.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))))))))))))))))
theorem ban_chunk_mem3 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk3.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))))))))))))))
theorem ban_chunk_mem4 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk4.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))))))))))))))
theorem ban_chunk_mem5 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk5.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))))))))))))
theorem ban_chunk_mem6 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk6.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))))))))))))
theorem ban_chunk_mem7 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk7.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))))))))))
theorem ban_chunk_mem8 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk8.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))))))))))
theorem ban_chunk_mem9 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk9.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))))))))
theorem ban_chunk_mem10 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk10.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))))))))
theorem ban_chunk_mem11 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk11.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))))))
theorem ban_chunk_mem12 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk12.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))))))
theorem ban_chunk_mem13 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk13.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))))
theorem ban_chunk_mem14 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk14.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))))
theorem ban_chunk_mem15 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk15.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))
theorem ban_chunk_mem16 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk16.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))
theorem ban_chunk_mem17 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk17.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))
theorem ban_chunk_mem18 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk18.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
theorem ban_chunk_mem19 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk19.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
theorem ban_chunk_mem20 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk20.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
theorem ban_chunk_mem21 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk21.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr h)))
theorem ban_chunk_mem22 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk22.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inr h))
theorem ban_chunk_mem23 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk23.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inl (Or.inr h)
theorem ban_chunk_mem24 (p : ℕ × ℕ) (h : p ∈ bannedPairArrayChunk24.toList) : p ∈ bannedPairArray.toList := by
  simp only [bannedPairArray, array_toList_append, List.mem_append]
  exact Or.inr h
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.ban_chunk_mem24
