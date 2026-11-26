import Lab.HenningYeo.GFl2

/-! Template facts for line `l = 3` (split by line to bound memory). -/

namespace OpenProblemsLab.HY

lemma gadget_leaf_unique_3 : ∀ a b, GValid 3 a b → ∀ z : Fin 10, deg (gadget 3 a b) z = 1 → z = 7 := by
  decide +kernel

lemma gadget_deg7_3 : ∀ a b, GValid 3 a b → deg (gadget 3 a b) 7 = 1 := by
  decide +kernel

lemma gadget_edge7_3 : ∀ a b, GValid 3 a b → ∀ f ∈ gadget 3 a b, 7 ∈ f → f = {7, 8, 9} := by
  decide +kernel

lemma gadget_deg89_3 : ∀ a b, GValid 3 a b → deg (gadget 3 a b) 8 = 2 ∧ deg (gadget 3 a b) 9 = 2 := by
  decide +kernel

lemma gadget_meet_3 : ∀ a b, GValid 3 a b → ∀ f₈ ∈ gadget 3 a b, 8 ∈ f₈ → f₈ ≠ {7, 8, 9} →
    ∀ f₉ ∈ gadget 3 a b, 9 ∈ f₉ → f₉ ≠ {7, 8, 9} →
      ∃ c ∈ f₈, c ∈ f₉ ∧ 3 ≤ deg (gadget 3 a b) c := by
  decide +kernel

lemma gadget_cover_3 : ∀ a b, GValid 3 a b → ∀ i : Fin 10, 1 ≤ deg (gadget 3 a b) i := by
  decide +kernel

end OpenProblemsLab.HY
