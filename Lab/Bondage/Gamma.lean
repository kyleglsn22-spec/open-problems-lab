import Lab.Bondage.GammaDefs
import Lab.Bondage.GPart0
import Lab.Bondage.GPart1
import Lab.Bondage.GPart2
import Lab.Bondage.GPart3
import Lab.Bondage.GPart4

/-!
# `γ(G) = 6` for Yavari's graph
-/

namespace OpenProblemsLab.Bondage

open Finset

theorem checkGa_eq : ∀ a, checkGa a = true := by
  intro a
  fin_cases a
  · exact checkGa_0
  · exact checkGa_1
  · exact checkGa_2
  · exact checkGa_3
  · exact checkGa_4
  · exact checkGa_5
  · exact checkGa_6
  · exact checkGa_7
  · exact checkGa_8
  · exact checkGa_9
  · exact checkGa_10
  · exact checkGa_11
  · exact checkGa_12
  · exact checkGa_13
  · exact checkGa_14
  · exact checkGa_15
  · exact checkGa_16
  · exact checkGa_17

/-- No dominating set has at most five vertices. -/
theorem six_le_card {D : Finset (Fin 18)} (hD : IsDominating G D) : 6 ≤ D.card := by
  by_contra h
  obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, hS⟩ := exists_sorted5 D (by omega) 0
  have hdom : domB [a, b, c, d, e] = true := by
    simp only [domB, List.all_eq_true, List.mem_finRange, true_implies, List.any_eq_true,
      List.contains_iff_mem]
    intro v
    rcases hD v with hv | ⟨u, hu, huv⟩
    · exact ⟨v, by rcases hS v hv with rfl | rfl | rfl | rfl | rfl <;> simp,
        (mem_nb v v).2 (Or.inl rfl)⟩
    · exact ⟨u, by rcases hS u hu with rfl | rfl | rfl | rfl | rfl <;> simp,
        (mem_nb u v).2 (Or.inr huv)⟩
  have := checkGa_eq a
  simp only [checkGa, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, not_le] at this
  rcases this b with h1 | h1
  · exact absurd hab (not_le.2 h1)
  rcases h1 c with h2 | h2
  · exact absurd hbc (not_le.2 h2)
  rcases h2 d with h3 | h3
  · exact absurd hcd (not_le.2 h3)
  rcases h3 e with h4 | h4
  · exact absurd hde (not_le.2 h4)
  · rw [hdom] at h4; exact Bool.noConfusion h4

/-- An explicit dominating 6-set (Yavari's `D₀`). -/
theorem isDominating_D0 : IsDominating G {0, 1, 2, 3, 14, 15} := by
  unfold IsDominating; decide

theorem dominationNumber_eq : dominationNumber G = 6 := by
  apply le_antisymm
  · exact (dominationNumber_le isDominating_D0).trans (by decide)
  · obtain ⟨D, hD, hc⟩ := exists_dominating_card G
    exact hc ▸ six_le_card hD

end OpenProblemsLab.Bondage
