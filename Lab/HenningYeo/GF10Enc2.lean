import Lab.HenningYeo.GF10Enc1

/-! Bitmask encoding agrees with `gadget 2 a b` (split by line to bound kernel memory). -/

namespace OpenProblemsLab.HY

lemma tmem_edge_2 : ∀ a b, GValid 2 a b → ∀ k : Fin 7, ∃ e ∈ gadget 2 a b,
    ∀ i : Fin 10, i ∈ e ↔ tmem 2 a b k i = true := by
  decide +kernel

lemma edge_tmem_2 : ∀ a b, GValid 2 a b → ∀ e ∈ gadget 2 a b, ∃ k : Fin 7,
    ∀ i : Fin 10, i ∈ e ↔ tmem 2 a b k i = true := by
  decide +kernel

lemma deg_tdg_2 : ∀ a b, GValid 2 a b → ∀ i, deg (gadget 2 a b) i = tdg 2 a b i := by
  decide +kernel

end OpenProblemsLab.HY
