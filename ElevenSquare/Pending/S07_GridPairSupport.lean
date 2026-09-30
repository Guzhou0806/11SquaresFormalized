import ElevenSquare.Pending.S07_GridLookupSupport
import ElevenSquare.Pending.S07_Data

namespace ElevenSquare.Pending.GridDistance

def indexedCheck (pr : ℕ × ℕ) : Bool := pairCheck gridArray[pr.1]! gridArray[pr.2]!

theorem pair_lookup_check (xs : Array (List GridPoint)) (i j : ℕ)
    (as bs : List GridPoint) (hi : xs[i]! = as) (hj : xs[j]! = bs)
    (h : pairCheck as bs = true) :
    pairCheck xs[(i,j).1]! xs[(i,j).2]! = true := by
  change pairCheck xs[i]! xs[j]! = true
  rw [hi, hj]
  exact h

theorem checks_append {xs ys : Array (ℕ × ℕ)}
    (hx : ∀ pr ∈ xs.toList, indexedCheck pr = true)
    (hy : ∀ pr ∈ ys.toList, indexedCheck pr = true) :
    ∀ pr ∈ (xs ++ ys).toList, indexedCheck pr = true := by
  intro pr hp
  simp only [Array.toList_append, List.mem_append] at hp
  rcases hp with hp | hp
  · exact hx pr hp
  · exact hy pr hp

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.pair_lookup_check
#print axioms ElevenSquare.Pending.GridDistance.checks_append
