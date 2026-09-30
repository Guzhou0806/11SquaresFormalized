import Sqpack.S11Opt.F00.Final
import Sqpack.S11Opt.F03.Final
import Sqpack.S11Opt.F06.Final
import Sqpack.S11Opt.F19.Final

namespace SquarePacking.S11Opt.ImportedFields

def direct (J : List ℕ) : Bool :=
  F00.supp.all (· ∈ J) || F03.applicable J || F06.applicable J || F19.applicable J

theorem direct_sound {J : List ℕ} (h : direct J = true) : CaseExcluded J := by
  simp only [direct, Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · intro hr
    exact F00.caseExcluded_supp (hr.mono (by simpa using h))
  · exact F03.applicable_sound h
  · exact F06.applicable_sound h
  · exact F19.applicable_sound h

def applicable (J : List ℕ) : Bool := direct J || direct (hmask J)

theorem applicable_sound {J : List ℕ} (hJ : ∀ j ∈ J, j < 16)
    (h : applicable J = true) : CaseExcluded J := by
  simp only [applicable, Bool.or_eq_true] at h
  rcases h with h | h
  · exact direct_sound h
  · intro hr
    exact direct_sound h (hr.hmask hJ)

end SquarePacking.S11Opt.ImportedFields

#print axioms SquarePacking.S11Opt.ImportedFields.applicable_sound
