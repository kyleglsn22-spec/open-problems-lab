import Lab.HenningYeo.GF10Enc2

/-! Bitmask encoding agrees with `gadget 3 a b` (split by line to bound kernel memory). -/

namespace OpenProblemsLab.HY

lemma tmem_edge_3 : ∀ a b, GValid 3 a b → ∀ k : Fin 7, ∃ e ∈ gadget 3 a b,
    ∀ i : Fin 10, i ∈ e ↔ tmem 3 a b k i = true := by
  decide +kernel

lemma edge_tmem_3 : ∀ a b, GValid 3 a b → ∀ e ∈ gadget 3 a b, ∃ k : Fin 7,
    ∀ i : Fin 10, i ∈ e ↔ tmem 3 a b k i = true := by
  decide +kernel

lemma deg_tdg_3 : ∀ a b, GValid 3 a b → ∀ i, deg (gadget 3 a b) i = tdg 3 a b i := by
  decide +kernel

end OpenProblemsLab.HY
