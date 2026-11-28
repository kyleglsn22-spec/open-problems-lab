import Lab.TightHamilton.Codeg

/-!
# The all-`n` exact codegree conjecture for tight Hamiltonian cycles is false

A `k`-uniform hypergraph (`k`-graph) has a **tight Hamiltonian cycle** if its vertices can be put
in a cyclic order in which every `k` cyclically consecutive vertices form an edge. The **codegree**
of a `(k - 1)`-set is the number of edges containing it.

**Conjecture** (Rödl, Ruciński and Szemerédi, Adv. Math. 2011, Conjecture 1.1, attributed to
Katona and Kierstead; also Oberwolfach Reports 2006 and 2008): every `k`-graph on
`n ≥ k + 1 ≥ 4` vertices with minimum codegree at least `⌊(n - k + 3)/2⌋` has a tight Hamiltonian
cycle.

A. Ferudun (Zenodo 10.5281/zenodo.23006717, September 2026) showed that this all-`n` form fails
for small `n`. Let `W = {0,…,5}` carry the ten faces of the hemi-icosahedron (the 6-vertex
triangulation of the real projective plane), and add `k - 2` apex vertices. The `k`-graph `H_k`
has as edges all `k`-sets meeting `W` in other than three points, and the `k`-sets meeting `W` in
a face. For `k = 3, 4, 5` (`n = 7, 8, 9`) it has minimum codegree `3 = ⌊7/2⌋` but no tight
Hamiltonian cycle. Ferudun reports that `H₃` (7 vertices) is the smallest possible counterexample
(exhaustive search; not formalized here).

Main results:
* `not_codegreeConjecture`: the conjecture is false;
* `H_counterexample`: `H_k` is a counterexample for each `k ∈ {3, 4, 5}`.

The no-cycle proof is modeled on Ferudun's Lemma 2.4, whose conclusion the kernel checks directly
over every set of apex positions: wherever the apexes sit in a cyclic order,
two `k`-windows contain exactly three points of `W` each, and those two triples are disjoint
(`ForcedPair`, checked by the kernel). Both would have to be faces, but any two faces of the
hemi-icosahedron meet (`Dface_meet`).
-/

namespace OpenProblemsLab.TightHamilton

open Finset

/-- Lemma 2.4 for `k = 5`, assembled from the cases split by the least apex position. -/
theorem forced5 : ForcedPair 5 := by
  intro P hP
  obtain ⟨-, hc⟩ := Finset.mem_powersetCard.1 hP
  have hne : P.Nonempty := Finset.card_pos.1 (by rw [hc]; norm_num)
  set a := P.min' hne
  have hall : ∀ a : Fin 9, Forced5At a := by
    intro a
    fin_cases a
    · exact forced5At_0
    · exact forced5At_1
    · exact forced5At_2
    · exact forced5At_3
    · exact forced5At_4
    · exact forced5At_5
    · exact forced5At_6
    all_goals (unfold Forced5At; decide +kernel)
  have hQ : P.erase a ∈ ((Finset.univ : Finset (Fin 9)).filter (a < ·)).powersetCard 2 := by
    refine Finset.mem_powersetCard.2 ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨hxa, hxP⟩ := Finset.mem_erase.1 hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
        lt_of_le_of_ne (P.min'_le x hxP) (Ne.symm hxa)⟩
    · rw [Finset.card_erase_of_mem (P.min'_mem hne), hc]
  have := hall a _ hQ
  rwa [Finset.insert_erase (P.min'_mem hne)] at this

theorem codegree_ge (k : ℕ) (hk : 1 ≤ k)
    (h : ∀ S : Finset (Fin (k + 4)), S.card = k - 1 →
      3 ≤ ((Finset.univ \ S).filter fun x => good (insert x S)).card) :
    ∀ S : Finset (Fin (k + 4)), S.card = k - 1 → 3 ≤ codegree (E k) S := by
  intro S hS
  rw [codegree_E_eq k S (by omega)]
  exact h S hS

/-- **Ferudun's counterexamples.** For `k ∈ {3, 4, 5}`, the `k`-graph `H_k` on `k + 4` vertices
is `k`-uniform, every `(k - 1)`-set has codegree at least `3 = ⌊((k + 4) - k + 3)/2⌋`, and `H_k`
has no tight Hamiltonian cycle. -/
theorem H_counterexample (k : ℕ) (hk : k = 3 ∨ k = 4 ∨ k = 5) :
    (∀ e ∈ E k, e.card = k) ∧
    (∀ S : Finset (Fin (k + 4)), S.card = k - 1 →
      (Fintype.card (Fin (k + 4)) - k + 3) / 2 ≤ codegree (E k) S) ∧
    ¬ HasTightHamiltonCycle (E k) k := by
  have hb : (Fintype.card (Fin (k + 4)) - k + 3) / 2 = 3 := by
    rw [Fintype.card_fin]; omega
  rw [hb]
  refine ⟨uniform_E k, ?_, ?_⟩
  · rcases hk with rfl | rfl | rfl
    · exact codegree_ge 3 (by norm_num) codeg3'
    · exact codegree_ge 4 (by norm_num) codeg4'
    · exact codegree_ge 5 (by norm_num) codeg5'
  · rcases hk with rfl | rfl | rfl
    · exact not_hasTightHamiltonCycle 3 (by decide) forced3
    · exact not_hasTightHamiltonCycle 4 (by decide) forced4
    · exact not_hasTightHamiltonCycle 5 (by decide) forced5

/-- **The all-`n` exact codegree conjecture for tight Hamiltonian cycles is false**: Ferudun's
7-vertex 3-graph `H₃` is a counterexample. -/
theorem not_codegreeConjecture : ¬ CodegreeConjecture := by
  intro h
  obtain ⟨hu, hc, hn⟩ := H_counterexample 3 (Or.inl rfl)
  exact hn (h 3 (Fin 7) (E 3) le_rfl (by simp) hu hc)

end OpenProblemsLab.TightHamilton
