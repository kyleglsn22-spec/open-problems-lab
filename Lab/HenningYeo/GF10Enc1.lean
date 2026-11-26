import Lab.HenningYeo.GF10Enc0

/-! Bitmask encoding agrees with `gadget 1 a b` (split by line to bound kernel memory). -/

namespace OpenProblemsLab.HY

lemma tmem_edge_1 : ∀ a b, GValid 1 a b → ∀ k : Fin 7, ∃ e ∈ gadget 1 a b,
    ∀ i : Fin 10, i ∈ e ↔ tmem 1 a b k i = true := by
  decide +kernel

lemma edge_tmem_1 : ∀ a b, GValid 1 a b → ∀ e ∈ gadget 1 a b, ∃ k : Fin 7,
    ∀ i : Fin 10, i ∈ e ↔ tmem 1 a b k i = true := by
  decide +kernel

lemma deg_tdg_1 : ∀ a b, GValid 1 a b → ∀ i, deg (gadget 1 a b) i = tdg 1 a b i := by
  decide +kernel

end OpenProblemsLab.HY
