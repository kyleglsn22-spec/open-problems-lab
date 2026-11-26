import Lab.HenningYeo.GF10Enc3

/-! Bitmask encoding agrees with `gadget 4 a b` (split by line to bound kernel memory). -/

namespace OpenProblemsLab.HY

lemma tmem_edge_4 : ∀ a b, GValid 4 a b → ∀ k : Fin 7, ∃ e ∈ gadget 4 a b,
    ∀ i : Fin 10, i ∈ e ↔ tmem 4 a b k i = true := by
  decide +kernel

lemma edge_tmem_4 : ∀ a b, GValid 4 a b → ∀ e ∈ gadget 4 a b, ∃ k : Fin 7,
    ∀ i : Fin 10, i ∈ e ↔ tmem 4 a b k i = true := by
  decide +kernel

lemma deg_tdg_4 : ∀ a b, GValid 4 a b → ∀ i, deg (gadget 4 a b) i = tdg 4 a b i := by
  decide +kernel

end OpenProblemsLab.HY
