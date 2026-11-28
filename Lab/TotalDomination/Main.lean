import Lab.TotalDomination.Drawing

/-! Part of claim GHT-1, see `Lab/TotalDomination/Basic.lean`. Main results. -/

namespace OpenProblemsLab.TotalDomination

open SimpleGraph Finset

/-- `B` has `102 = 3 · 36 - 6` edges, so with its planar drawing it is a triangulation. -/
theorem card_edgeFinset_B : B.edgeFinset.card = 102 := by
  have h := B.sum_degrees_eq_twice_card_edges
  have hd : ∑ v, B.degree v = 204 := by
    simp only [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    decide +kernel
  omega

/-- **Kwon–Park–Sano, Theorem 1.2 for `n = 36`**: the planar triangulation `B` has no partition
into two total dominating sets that both induce bipartite subgraphs. -/
theorem B_counterexample :
    ¬ ∃ A : Set (Fin 36), IsTotalDominating B A ∧ IsTotalDominating B Aᶜ ∧
      (B.induce A).Colorable 2 ∧ (B.induce Aᶜ).Colorable 2 := by
  rintro ⟨A, h1, h2, c1, c2⟩
  obtain ⟨c, hp, hnd⟩ := partnerColoring_of_partition B A h1 h2 c1 c2
  exact no_partner_coloring_B c (fun u v h => hp u v h) hnd

/-- **Goddard–Henning Conjecture 32 is false.** -/
theorem not_goddardHenningConjecture : ¬ GoddardHenningConjecture := by
  intro h
  exact B_counterexample (h 36 B (by norm_num) straightLinePlanar_B card_edgeFinset_B)

end OpenProblemsLab.TotalDomination
