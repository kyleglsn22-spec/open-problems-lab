import Lab.HenningYeo.GFl4

/-!
# Structure of the hypergraphs `H₁₀`, `H₁₀'`: facts about the templates (by `decide`, per line)
-/

namespace OpenProblemsLab.HY

lemma gadget_leaf_unique : ∀ l a b, GValid l a b → ∀ z : Fin 10, deg (gadget l a b) z = 1 → z = 7 := by
  intro l
  fin_cases l
  · exact gadget_leaf_unique_0
  · exact gadget_leaf_unique_1
  · exact gadget_leaf_unique_2
  · exact gadget_leaf_unique_3
  · exact gadget_leaf_unique_4

lemma gadget_deg7 : ∀ l a b, GValid l a b → deg (gadget l a b) 7 = 1 := by
  intro l
  fin_cases l
  · exact gadget_deg7_0
  · exact gadget_deg7_1
  · exact gadget_deg7_2
  · exact gadget_deg7_3
  · exact gadget_deg7_4

lemma gadget_edge7 : ∀ l a b, GValid l a b → ∀ f ∈ gadget l a b, 7 ∈ f → f = {7, 8, 9} := by
  intro l
  fin_cases l
  · exact gadget_edge7_0
  · exact gadget_edge7_1
  · exact gadget_edge7_2
  · exact gadget_edge7_3
  · exact gadget_edge7_4

lemma gadget_deg89 : ∀ l a b, GValid l a b → deg (gadget l a b) 8 = 2 ∧ deg (gadget l a b) 9 = 2 := by
  intro l
  fin_cases l
  · exact gadget_deg89_0
  · exact gadget_deg89_1
  · exact gadget_deg89_2
  · exact gadget_deg89_3
  · exact gadget_deg89_4

lemma gadget_meet : ∀ l a b, GValid l a b → ∀ f₈ ∈ gadget l a b, 8 ∈ f₈ → f₈ ≠ {7, 8, 9} →
    ∀ f₉ ∈ gadget l a b, 9 ∈ f₉ → f₉ ≠ {7, 8, 9} →
      ∃ c ∈ f₈, c ∈ f₉ ∧ 3 ≤ deg (gadget l a b) c := by
  intro l
  fin_cases l
  · exact gadget_meet_0
  · exact gadget_meet_1
  · exact gadget_meet_2
  · exact gadget_meet_3
  · exact gadget_meet_4

lemma gadget_cover : ∀ l a b, GValid l a b → ∀ i : Fin 10, 1 ≤ deg (gadget l a b) i := by
  intro l
  fin_cases l
  · exact gadget_cover_0
  · exact gadget_cover_1
  · exact gadget_cover_2
  · exact gadget_cover_3
  · exact gadget_cover_4

end OpenProblemsLab.HY
