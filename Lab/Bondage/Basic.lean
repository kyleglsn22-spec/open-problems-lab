import Mathlib

/-!
# Teschner's bondage-number conjecture: definitions and Yavari's graph

A set `D` **dominates** a graph if every vertex is in `D` or adjacent to a vertex of `D`; the
**domination number** `γ(G)` is the least size of such a set. The **bondage number** `b(G)`
(Fink–Jacobson–Kinch–Roberts 1990) is the least number of edges whose deletion increases `γ`.

U. Teschner (Australas. J. Combin. 12 (1995)) conjectured `b(G) ≤ (3/2) Δ(G)` for every finite
graph with at least one edge. Y. Yavari (arXiv:2609.04257) disproved it with a connected cubic
bipartite graph on 18 vertices with `γ = 6` and `b = 5 > 9/2`.

This file holds the definitions, the graph, and the generic lemmas; the finite checks are in
`Gamma.lean` and `Quads.lean`, and the main theorem in `Main.lean`.
-/

namespace OpenProblemsLab.Bondage

open SimpleGraph Finset

section General

variable {V : Type*} [Fintype V]

/-- `D` dominates `G`: every vertex is in `D` or has a neighbour in `D`. -/
def IsDominating (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, v ∈ D ∨ ∃ u ∈ D, G.Adj v u

/-- The domination number `γ(G)`. -/
noncomputable def dominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : Finset V, IsDominating G D ∧ D.card = k}

/-- The bondage number `b(G)`: the least size of an edge set whose deletion increases `γ`. -/
noncomputable def bondageNumber (G : SimpleGraph V) [DecidableEq V] : ℕ :=
  sInf {k | ∃ F : Finset (Sym2 V), (↑F : Set (Sym2 V)) ⊆ G.edgeSet ∧ F.card = k ∧
    dominationNumber G < dominationNumber (G.deleteEdges ↑F)}

theorem isDominating_univ (G : SimpleGraph V) : IsDominating G Finset.univ :=
  fun v => Or.inl (Finset.mem_univ v)

omit [Fintype V] in
theorem dominationNumber_le {G : SimpleGraph V} {D : Finset V} (hD : IsDominating G D) :
    dominationNumber G ≤ D.card :=
  Nat.sInf_le ⟨D, hD, rfl⟩

theorem exists_dominating_card (G : SimpleGraph V) :
    ∃ D : Finset V, IsDominating G D ∧ D.card = dominationNumber G := by
  have h : ({k | ∃ D : Finset V, IsDominating G D ∧ D.card = k} : Set ℕ).Nonempty :=
    ⟨_, Finset.univ, isDominating_univ G, rfl⟩
  exact Nat.sInf_mem h

end General

/-- **Teschner's conjecture** (1995): every finite graph with at least one edge has
`b(G) ≤ (3/2) Δ(G)`. -/
def TeschnerConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.edgeSet.Nonempty → (bondageNumber G : ℚ) ≤ 3 / 2 * G.maxDegree

/-! ## Yavari's graph -/

/-- The 27 edges (Yavari, Appendix A). -/
def edges : List (Fin 18 × Fin 18) :=
  [(0, 6), (0, 10), (0, 16), (1, 8), (1, 11), (1, 12), (2, 4), (2, 5), (2, 13), (3, 4), (3, 5),
   (3, 9), (4, 16), (5, 11), (6, 7), (6, 13), (7, 8), (7, 14), (8, 13), (9, 10), (9, 14),
   (10, 15), (11, 15), (12, 15), (12, 17), (14, 17), (16, 17)]

theorem edges_length : edges.length = 27 := rfl

/-- Adjacency as a Boolean test. -/
def adjB (u v : Fin 18) : Bool := edges.contains (u, v) || edges.contains (v, u)

/-- Yavari's graph. -/
def G : SimpleGraph (Fin 18) where
  Adj u v := adjB u v = true
  symm := ⟨fun u v h => by simpa [adjB, Bool.or_comm] using h⟩
  loopless := ⟨fun u h => by revert u h; decide⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (adjB u v = true))

/-- The `i`-th edge, as a pair. -/
def ePair (i : Fin 27) : Fin 18 × Fin 18 := edges.get ⟨i, by simp [edges_length]⟩

/-- The `i`-th edge. -/
def edgeAt (i : Fin 27) : Sym2 (Fin 18) := s((ePair i).1, (ePair i).2)

theorem edgeAt_injective : Function.Injective edgeAt := by
  intro i j h
  revert i j h
  decide

theorem adj_ePair (i : Fin 27) : G.Adj (ePair i).1 (ePair i).2 := by
  revert i; decide

/-- Every edge of `G` is one of the 27 listed edges. -/
theorem exists_edgeAt {e : Sym2 (Fin 18)} (he : e ∈ G.edgeSet) : ∃ i, edgeAt i = e := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeSet] at he
    revert u v he
    decide

/-- Closed neighbourhoods, as a lookup table. -/
def nb : Fin 18 → List (Fin 18) :=
  ![[0, 6, 10, 16], [1, 8, 11, 12], [2, 4, 5, 13], [3, 4, 5, 9], [4, 2, 3, 16], [5, 2, 3, 11],
    [6, 0, 7, 13], [7, 6, 8, 14], [8, 1, 7, 13], [9, 3, 10, 14], [10, 0, 9, 15],
    [11, 1, 5, 15], [12, 1, 15, 17], [13, 2, 6, 8], [14, 7, 9, 17], [15, 10, 11, 12],
    [16, 0, 4, 17], [17, 12, 14, 16]]

theorem mem_nb (u v : Fin 18) : v ∈ nb u ↔ v = u ∨ G.Adj v u := by
  revert u v; decide

/-- `G` is cubic. -/
theorem degree_eq (v : Fin 18) : G.degree v = 3 := by
  revert v; decide

theorem maxDegree_eq : G.maxDegree = 3 :=
  le_antisymm (G.maxDegree_le_of_forall_degree_le 3 fun v => (degree_eq v).le)
    (degree_eq 0 ▸ G.degree_le_maxDegree 0)

/-! ## Sorting small finsets -/

theorem exists_sorted4 {n : ℕ} (S : Finset (Fin n)) (h : S.card ≤ 4) (x₀ : Fin n) :
    ∃ a b c d : Fin n, a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ ∀ x ∈ S, x = a ∨ x = b ∨ x = c ∨ x = d := by
  have hs := Finset.pairwise_sort S (fun x y : Fin n => x ≤ y)
  have hl : (S.sort (fun x y : Fin n => x ≤ y)).length = S.card := Finset.length_sort _
  have hm : ∀ x, x ∈ S ↔ x ∈ S.sort (fun x y : Fin n => x ≤ y) := fun x => (Finset.mem_sort _).symm
  generalize S.sort (fun x y : Fin n => x ≤ y) = l at hs hl hm
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩
  · exact ⟨x₀, x₀, x₀, x₀, le_rfl, le_rfl, le_rfl, fun x hx => by simp [hm] at hx⟩
  · exact ⟨a, a, a, a, le_rfl, le_rfl, le_rfl, fun x hx => by simp [hm] at hx; simp [hx]⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hs
    exact ⟨a, b, b, b, hs.1, le_rfl, le_rfl, fun x hx => by
      simp [hm] at hx; rcases hx with rfl | rfl <;> simp⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hs
    exact ⟨a, b, c, c, hs.1.1, hs.2.1, le_rfl, fun x hx => by
      simp [hm] at hx; rcases hx with rfl | rfl | rfl <;> simp⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hs
    exact ⟨a, b, c, d, hs.1.1, hs.2.1.1, hs.2.2.1, fun x hx => by
      simp [hm] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp⟩
  · simp at hl; omega

theorem exists_sorted5 {n : ℕ} (S : Finset (Fin n)) (h : S.card ≤ 5) (x₀ : Fin n) :
    ∃ a b c d e : Fin n, a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧
      ∀ x ∈ S, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
  have hs := Finset.pairwise_sort S (fun x y : Fin n => x ≤ y)
  have hl : (S.sort (fun x y : Fin n => x ≤ y)).length = S.card := Finset.length_sort _
  have hm : ∀ x, x ∈ S ↔ x ∈ S.sort (fun x y : Fin n => x ≤ y) := fun x => (Finset.mem_sort _).symm
  generalize S.sort (fun x y : Fin n => x ≤ y) = l at hs hl hm
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, l⟩⟩⟩⟩⟩⟩
  · exact ⟨x₀, x₀, x₀, x₀, x₀, le_rfl, le_rfl, le_rfl, le_rfl, fun x hx => by simp [hm] at hx⟩
  · exact ⟨a, a, a, a, a, le_rfl, le_rfl, le_rfl, le_rfl, fun x hx => by simp [hm] at hx; simp [hx]⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hs
    exact ⟨a, b, b, b, b, hs.1, le_rfl, le_rfl, le_rfl, fun x hx => by
      simp [hm] at hx; rcases hx with rfl | rfl <;> simp⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hs
    exact ⟨a, b, c, c, c, hs.1.1, hs.2.1, le_rfl, le_rfl, fun x hx => by
      simp [hm] at hx; rcases hx with rfl | rfl | rfl <;> simp⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hs
    exact ⟨a, b, c, d, d, hs.1.1, hs.2.1.1, hs.2.2.1, le_rfl, fun x hx => by
      simp [hm] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hs
    exact ⟨a, b, c, d, e, by tauto, by tauto, by tauto, by tauto, fun x hx => by
      simp [hm] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp⟩
  · simp at hl; omega

end OpenProblemsLab.Bondage
