import Lab.TotalDomination.Basic

/-! Part of claim GHT-1, see `Lab/TotalDomination/Basic.lean`. -/

namespace OpenProblemsLab.TotalDomination

open SimpleGraph

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Lemma 3.1 of Kwon–Park–Sano in nested form (the order of the variables lets the kernel prune
improper partial colourings early): in a proper colouring of `G₁₄` in which `v₃`, `v₅`, `v₉` are
not defective, `v₀v₂` is not a partner edge. -/
theorem lemma31 :
    ∀ x0 : Fin 4,
    ∀ x2 : Fin 4,
    x0 ≠ x2 →
    x2 = partner x0 →
    ∀ x1 : Fin 4,
    x0 ≠ x1 →
    x2 ≠ x1 →
    ∀ x3 : Fin 4,
    x0 ≠ x3 →
    x2 ≠ x3 →
    ∀ x4 : Fin 4,
    x0 ≠ x4 →
    x3 ≠ x4 →
    ∀ x11 : Fin 4,
    x2 ≠ x11 →
    x3 ≠ x11 →
    x4 ≠ x11 →
    (x0 = partner x3 ∨ x2 = partner x3 ∨ x4 = partner x3 ∨ x11 = partner x3) →
    ∀ x5 : Fin 4,
    x0 ≠ x5 →
    x4 ≠ x5 →
    ∀ x12 : Fin 4,
    x4 ≠ x12 →
    x11 ≠ x12 →
    x5 ≠ x12 →
    ∀ x6 : Fin 4,
    x0 ≠ x6 →
    x5 ≠ x6 →
    x12 ≠ x6 →
    (x0 = partner x5 ∨ x4 = partner x5 ∨ x6 = partner x5 ∨ x12 = partner x5) →
    ∀ x10 : Fin 4,
    x2 ≠ x10 →
    x11 ≠ x10 →
    x12 ≠ x10 →
    x6 ≠ x10 →
    ∀ x7 : Fin 4,
    x0 ≠ x7 →
    x1 ≠ x7 →
    x6 ≠ x7 →
    ∀ x8 : Fin 4,
    x2 ≠ x8 →
    x1 ≠ x8 →
    x10 ≠ x8 →
    ∀ x13 : Fin 4,
    x6 ≠ x13 →
    x10 ≠ x13 →
    x7 ≠ x13 →
    x8 ≠ x13 →
    ∀ x9 : Fin 4,
    x1 ≠ x9 →
    x7 ≠ x9 →
    x8 ≠ x9 →
    x13 ≠ x9 →
    (x1 = partner x9 ∨ x7 = partner x9 ∨ x8 = partner x9 ∨ x13 = partner x9) →
    False := by
  decide +kernel

end OpenProblemsLab.TotalDomination
