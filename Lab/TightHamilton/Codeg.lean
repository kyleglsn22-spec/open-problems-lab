import Lab.TightHamilton.Forced5d

/-! Minimum codegree 3 of `H₃`, `H₄`, `H₅` (via `codegree_E_eq`), checked by the kernel. -/

namespace OpenProblemsLab.TightHamilton

open Finset

theorem codeg3' : ∀ S : Finset (Fin 7), S.card = 2 →
    3 ≤ ((Finset.univ \ S).filter fun x => good (insert x S)).card := by decide +kernel

theorem codeg4' : ∀ S : Finset (Fin 8), S.card = 3 →
    3 ≤ ((Finset.univ \ S).filter fun x => good (insert x S)).card := by decide +kernel

theorem codeg5' : ∀ S : Finset (Fin 9), S.card = 4 →
    3 ≤ ((Finset.univ \ S).filter fun x => good (insert x S)).card := by decide +kernel

end OpenProblemsLab.TightHamilton
