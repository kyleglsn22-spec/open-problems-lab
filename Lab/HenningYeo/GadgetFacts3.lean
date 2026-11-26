import Lab.HenningYeo.GF10Enc4

/-!
# The bitmask encoding of the templates agrees with `gadget`
-/

namespace OpenProblemsLab.HY

lemma tmem_edge : ∀ l a b, GValid l a b → ∀ k : Fin 7, ∃ e ∈ gadget l a b,
    ∀ i : Fin 10, i ∈ e ↔ tmem l a b k i = true := by
  intro l
  fin_cases l
  · exact tmem_edge_0
  · exact tmem_edge_1
  · exact tmem_edge_2
  · exact tmem_edge_3
  · exact tmem_edge_4

lemma edge_tmem : ∀ l a b, GValid l a b → ∀ e ∈ gadget l a b, ∃ k : Fin 7,
    ∀ i : Fin 10, i ∈ e ↔ tmem l a b k i = true := by
  intro l
  fin_cases l
  · exact edge_tmem_0
  · exact edge_tmem_1
  · exact edge_tmem_2
  · exact edge_tmem_3
  · exact edge_tmem_4

lemma deg_tdg : ∀ l a b, GValid l a b → ∀ i, deg (gadget l a b) i = tdg l a b i := by
  intro l
  fin_cases l
  · exact deg_tdg_0
  · exact deg_tdg_1
  · exact deg_tdg_2
  · exact deg_tdg_3
  · exact deg_tdg_4

end OpenProblemsLab.HY
