import Lab.HenningYeo.GadgetFacts2

/-! Bitmask encoding agrees with `gadget 0 a b` (split by line to bound kernel memory). -/

namespace OpenProblemsLab.HY

lemma tmem_edge_0 : ∀ a b, GValid 0 a b → ∀ k : Fin 7, ∃ e ∈ gadget 0 a b,
    ∀ i : Fin 10, i ∈ e ↔ tmem 0 a b k i = true := by
  decide +kernel

lemma edge_tmem_0 : ∀ a b, GValid 0 a b → ∀ e ∈ gadget 0 a b, ∃ k : Fin 7,
    ∀ i : Fin 10, i ∈ e ↔ tmem 0 a b k i = true := by
  decide +kernel

lemma deg_tdg_0 : ∀ a b, GValid 0 a b → ∀ i, deg (gadget 0 a b) i = tdg 0 a b i := by
  decide +kernel

end OpenProblemsLab.HY
