import Lab.Bondage.Gamma
import Lab.Bondage.QuadsAll

/-!
# Teschner's bondage-number conjecture is false

Yavari's cubic graph `G` on 18 vertices (arXiv:2609.04257) has `γ(G) = 6` (`Gamma.lean`) and
bondage number `b(G) = 5 > 9/2 = (3/2) Δ(G)`:
* deleting the five edges at the adjacent vertices `0` and `6` raises `γ` to at least 7
  (`seven_le_dominationNumber_F5`; both vertices become isolated, and a dominating set of the rest
  would give a dominating 5-set of `G` after adding `0`);
* deleting any four edges leaves some minimum dominating set dominating (`QuadsAll.lean`).

Main result: `not_teschnerConjecture`.
-/

namespace OpenProblemsLab.Bondage

open SimpleGraph Finset

/-- The five edges at `0` and `6`: `06, 0 10, 0 16, 67, 6 13`. -/
def F5 : Finset (Sym2 (Fin 18)) := {edgeAt 0, edgeAt 1, edgeAt 2, edgeAt 14, edgeAt 15}

theorem F5_subset : (↑F5 : Set (Sym2 (Fin 18))) ⊆ G.edgeSet := by
  intro e he
  simp only [F5, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> exact adj_ePair _

theorem card_F5 : F5.card = 5 := by decide

theorem isolated_F5 (u : Fin 18) :
    ¬ (G.deleteEdges ↑F5).Adj 0 u ∧ ¬ (G.deleteEdges ↑F5).Adj 6 u := by
  simp only [deleteEdges_adj, Finset.mem_coe]
  revert u; decide

/-- Deleting `F5` raises the domination number to at least 7. -/
theorem seven_le_dominationNumber_F5 : 7 ≤ dominationNumber (G.deleteEdges ↑F5) := by
  obtain ⟨D, hD, hc⟩ := exists_dominating_card (G.deleteEdges ↑F5)
  have h0 : (0 : Fin 18) ∈ D := by
    rcases hD 0 with h | ⟨u, -, hu⟩
    · exact h
    · exact absurd hu (isolated_F5 u).1
  have h6 : (6 : Fin 18) ∈ D := by
    rcases hD 6 with h | ⟨u, -, hu⟩
    · exact h
    · exact absurd hu (isolated_F5 u).2
  have hD' : IsDominating G (D.erase 6) := by
    intro v
    by_cases hv6 : v = 6
    · subst hv6
      exact Or.inr ⟨0, Finset.mem_erase.2 ⟨by decide, h0⟩, by decide⟩
    rcases hD v with hv | ⟨u, hu, huv⟩
    · exact Or.inl (Finset.mem_erase.2 ⟨hv6, hv⟩)
    · have hu6 : u ≠ 6 := by
        rintro rfl
        exact (isolated_F5 v).2 huv.symm
      exact Or.inr ⟨u, Finset.mem_erase.2 ⟨hu6, hu⟩, (deleteEdges_adj.1 huv).1⟩
  have := six_le_card hD'
  rw [Finset.card_erase_of_mem h6] at this
  omega

/-- From the per-row checks: every sorted quadruple has a surviving listed set. -/
theorem okQ_of_sorted {a b c d : Fin 27} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    okQ a b c d = true := by
  have h := checkQab_all a b hab
  simp only [checkQab, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, not_le] at h
  rcases h c with h1 | h1
  · exact absurd hbc (not_le.2 h1)
  rcases h1 d with h2 | h2
  · exact absurd hcd (not_le.2 h2)
  · exact h2

/-- If no deleted edge is outside `{a, b, c, d}` and a listed set survives, that set still
dominates. -/
theorem isDominating_of_survB {F : Finset (Sym2 (Fin 18))} {a b c d : Fin 27}
    (hF : ∀ e ∈ F, e = edgeAt a ∨ e = edgeAt b ∨ e = edgeAt c ∨ e = edgeAt d)
    {p : List (Fin 18) × List (Fin 18 × List (Fin 27))} (hp : p ∈ Ls)
    (hs : survB p a b c d = true) : IsDominating (G.deleteEdges ↑F) p.1.toFinset := by
  have hv := validL_eq
  simp only [validL, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_finRange,
    true_implies, Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem] at hv
  obtain ⟨⟨-, hcov⟩, hedge⟩ := hv p hp
  simp only [survB, List.all_eq_true, List.any_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    beq_eq_false_iff_ne] at hs
  intro x
  rcases hcov x with hx | ⟨q, hq, rfl⟩
  · exact Or.inl (List.mem_toFinset.2 hx)
  obtain ⟨i, hi, hne⟩ := hs q hq
  have hnot : edgeAt i ∉ F := by
    intro h
    rcases hF _ h with h | h | h | h <;>
      (have := edgeAt_injective h; subst this; simp at hne)
  have hadj := adj_ePair i
  rcases hedge q hq i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inr ⟨(ePair i).2, List.mem_toFinset.2 h2, deleteEdges_adj.2 ⟨h1 ▸ hadj, ?_⟩⟩
    rw [Finset.mem_coe, ← h1]; exact hnot
  · refine Or.inr ⟨(ePair i).1, List.mem_toFinset.2 h2, deleteEdges_adj.2 ⟨h1 ▸ hadj.symm, ?_⟩⟩
    rw [Finset.mem_coe, ← h1, Sym2.eq_swap]; exact hnot

/-- Deleting at most four edges never increases the domination number. -/
theorem dominationNumber_delete_le {F : Finset (Sym2 (Fin 18))}
    (hFE : (↑F : Set (Sym2 (Fin 18))) ⊆ G.edgeSet) (hF : F.card ≤ 4) :
    dominationNumber (G.deleteEdges ↑F) ≤ 6 := by
  set S := Finset.univ.filter (fun i : Fin 27 => edgeAt i ∈ F)
  have hS : S.card ≤ 4 := (Finset.card_le_card_of_injOn edgeAt
    (fun i hi => (Finset.mem_filter.1 hi).2) (fun i _ j _ h => edgeAt_injective h)).trans hF
  obtain ⟨a, b, c, d, hab, hbc, hcd, habcd⟩ := exists_sorted4 S hS 0
  have hF' : ∀ e ∈ F, e = edgeAt a ∨ e = edgeAt b ∨ e = edgeAt c ∨ e = edgeAt d := by
    intro e he
    obtain ⟨i, rfl⟩ := exists_edgeAt (hFE he)
    rcases habcd i (Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩) with rfl | rfl | rfl | rfl <;>
      simp
  have hok := okQ_of_sorted hab hbc hcd
  simp only [okQ, List.any_eq_true] at hok
  obtain ⟨p, hp, hs⟩ := hok
  have hlen : p.1.length = 6 := by
    have hv := validL_eq
    simp only [validL, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hv
    exact (hv p hp).1.1
  calc dominationNumber (G.deleteEdges ↑F) ≤ p.1.toFinset.card :=
        dominationNumber_le (isDominating_of_survB hF' hp hs)
    _ ≤ p.1.length := List.toFinset_card_le _
    _ = 6 := hlen

/-- **Yavari's Theorem 1.2.** `b(G) = 5`. -/
theorem bondageNumber_eq : bondageNumber G = 5 := by
  have hmem : 5 ∈ {k | ∃ F : Finset (Sym2 (Fin 18)), (↑F : Set (Sym2 (Fin 18))) ⊆ G.edgeSet ∧
      F.card = k ∧ dominationNumber G < dominationNumber (G.deleteEdges ↑F)} :=
    ⟨F5, F5_subset, card_F5, by rw [dominationNumber_eq]; have := seven_le_dominationNumber_F5; omega⟩
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨5, hmem⟩
  rintro k ⟨F, hFE, rfl, hlt⟩
  by_contra h
  have := dominationNumber_delete_le hFE (by omega)
  rw [dominationNumber_eq] at hlt
  omega

/-- Teschner's conjecture is false: `b(G) = 5 > 9/2 = (3/2) Δ(G)`. -/
theorem not_teschnerConjecture : ¬ TeschnerConjecture := by
  intro h
  have := h (Fin 18) G ⟨edgeAt 0, adj_ePair 0⟩
  rw [bondageNumber_eq, maxDegree_eq] at this
  norm_num at this

end OpenProblemsLab.Bondage
