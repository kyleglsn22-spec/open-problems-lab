import Mathlib

/-!
# Spanning forests: the Bencs–Csikvári degree-product conjecture is false

For a finite simple graph `G` let `F(G)` be the number of spanning forests (acyclic spanning
subgraphs, i.e. acyclic edge subsets). Bencs and Csikvári proved `F(G) ≤ r^n` for `r`-regular
graphs (`r ≥ 2`; European J. Combin. 2023) and conjectured that every graph with minimum degree at least `3` satisfies
`F(G) ≤ ∏_v deg(v)`.

Wu, Lu and Dong (arXiv:2611.18076, "Upper bounds for the number of spanning forests of a graph",
Section 1, after Conjecture 1.1) disprove this with complete bipartite graphs: in `K_{a,b}` every vertex of the
`b`-side may stay isolated or join one of the `a` vertices, which gives `(a+1)^b` distinct
spanning forests, while `∏ deg = b^a a^b`. For fixed `a ≥ 3` and large `b` the forests win.

* `card_le_numSpanningForests`: `(a+1)^b ≤ F(K_{a,b})`.
* `prod_degree`: `∏ deg = b^a · a^b` in `K_{a,b}`.
* `not_conjecture`: `K_{3,38}` is a counterexample (`4^38 > 38^3 · 3^38`).
* `counterexample_for_every_a`: for every `a ≥ 3` there is a counterexample `K_{a,b}` (we use
  `b = 4a³`), as in the paper.

(The paper's smallest concrete example `K_{3,14}` uses an exact enumeration formula of Stark;
our elementary lower bound needs `b ≥ 38` when `a = 3`.)
-/

namespace OpenProblemsLab.SpanningForests

open Finset SimpleGraph

/-- The number of spanning forests of `G`: edge subsets `S ⊆ E(G)` whose graph is acyclic. -/
noncomputable def numSpanningForests {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := by
  classical
  exact (G.edgeFinset.powerset.filter fun S : Finset (Sym2 V) =>
    (fromEdgeSet (↑S : Set (Sym2 V))).IsAcyclic).card

/-- **Conjecture (Bencs–Csikvári)**: if every vertex has degree at least `3`, then
`F(G) ≤ ∏_v deg(v)`. -/
def Conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, 3 ≤ G.degree v) → numSpanningForests G ≤ ∏ v, G.degree v

variable {a b : ℕ}

/-- `K_{a,b}` with vertex set `Fin a ⊕ Fin b`. -/
abbrev K (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) := completeBipartiteGraph (Fin a) (Fin b)

instance (a b : ℕ) : DecidableRel (K a b).Adj := fun u v => by
  simp only [K, completeBipartiteGraph]; infer_instance

lemma degree_inl (i : Fin a) : (K a b).degree (Sum.inl i) = b := by
  rw [← card_neighborFinset_eq_degree]
  have : (K a b).neighborFinset (Sum.inl i) = univ.map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext v; rcases v with j | j <;> simp
  rw [this]; simp

lemma degree_inr (j : Fin b) : (K a b).degree (Sum.inr j) = a := by
  rw [← card_neighborFinset_eq_degree]
  have : (K a b).neighborFinset (Sum.inr j) = univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext v; rcases v with i | i <;> simp
  rw [this]; simp

/-- `∏ deg = b^a · a^b` in `K_{a,b}`. -/
lemma prod_degree : ∏ v, (K a b).degree v = b ^ a * a ^ b := by
  rw [Fintype.prod_sum_type]
  simp [degree_inl, degree_inr]

/-- The star forest of `f : Fin b → Option (Fin a)`: `inr j` is joined to `inl i` iff
`f j = some i`. -/
def starForest (f : Fin b → Option (Fin a)) : SimpleGraph (Fin a ⊕ Fin b) :=
  SimpleGraph.fromRel fun u v => ∃ i j, u = Sum.inl i ∧ v = Sum.inr j ∧ f j = some i

@[simp] lemma starForest_adj_inl_inr {f : Fin b → Option (Fin a)} {i : Fin a} {j : Fin b} :
    (starForest f).Adj (Sum.inl i) (Sum.inr j) ↔ f j = some i := by
  simp [starForest]

@[simp] lemma starForest_adj_inr_inl {f : Fin b → Option (Fin a)} {i : Fin a} {j : Fin b} :
    (starForest f).Adj (Sum.inr j) (Sum.inl i) ↔ f j = some i := by
  simp [starForest]

@[simp] lemma starForest_not_adj_inl_inl {f : Fin b → Option (Fin a)} {i i' : Fin a} :
    ¬ (starForest f).Adj (Sum.inl i) (Sum.inl i') := by
  simp [starForest]

@[simp] lemma starForest_not_adj_inr_inr {f : Fin b → Option (Fin a)} {j j' : Fin b} :
    ¬ (starForest f).Adj (Sum.inr j) (Sum.inr j') := by
  simp [starForest]

lemma starForest_le (f : Fin b → Option (Fin a)) : starForest f ≤ K a b := by
  intro u v h
  rcases u with i | j <;> rcases v with i' | j' <;> simp_all

/-- Every edge `inl i — inr j` of a star forest is a bridge: `inr j` has no other neighbour. -/
lemma isBridge_starForest {f : Fin b → Option (Fin a)} {i : Fin a} {j : Fin b}
    (h : f j = some i) : (starForest f).IsBridge s(Sum.inl i, Sum.inr j) := by
  rw [isBridge_iff]
  apply not_reachable_of_neighborSet_right_eq_empty (by simp)
  ext v
  simp only [mem_neighborSet, deleteEdges_adj, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and, not_not]
  intro hv
  rcases v with i' | j'
  · rw [starForest_adj_inr_inl, h, Option.some_inj] at hv
    subst hv
    exact Sym2.eq_swap
  · simp at hv

lemma starForest_isAcyclic (f : Fin b → Option (Fin a)) : (starForest f).IsAcyclic := by
  refine isAcyclic_iff_forall_adj_isBridge.mpr fun u v huv => ?_
  rcases u with i | j <;> rcases v with i' | j'
  · simp at huv
  · exact isBridge_starForest (starForest_adj_inl_inr.1 huv)
  · rw [Sym2.eq_swap]; exact isBridge_starForest (starForest_adj_inr_inl.1 huv)
  · simp at huv

lemma starForest_injective : Function.Injective (starForest : (Fin b → Option (Fin a)) → _) := by
  intro f g hfg
  funext j
  cases hf : f j with
  | some i =>
    have : (starForest f).Adj (Sum.inl i) (Sum.inr j) := by simp [hf]
    rw [hfg, starForest_adj_inl_inr] at this
    exact this.symm
  | none =>
    cases hg : g j with
    | none => rfl
    | some i =>
      have : (starForest g).Adj (Sum.inl i) (Sum.inr j) := by simp [hg]
      rw [← hfg, starForest_adj_inl_inr, hf] at this
      exact absurd this (by simp)

/-- **`(a+1)^b ≤ F(K_{a,b})`.** -/
theorem card_le_numSpanningForests : (a + 1) ^ b ≤ numSpanningForests (K a b) := by
  classical
  unfold numSpanningForests
  have hcard : Fintype.card (Fin b → Option (Fin a)) = (a + 1) ^ b := by simp
  rw [← hcard, ← card_univ]
  refine card_le_card_of_injOn (fun f => (starForest f).edgeFinset) ?_ ?_
  · intro f _
    simp only [mem_coe, mem_filter, mem_powerset]
    refine ⟨edgeFinset_mono (starForest_le f), ?_⟩
    rw [coe_edgeFinset, fromEdgeSet_edgeSet]
    exact starForest_isAcyclic f
  · intro f _ g _ hfg
    apply starForest_injective
    rw [← edgeSet_inj, ← coe_edgeFinset, ← coe_edgeFinset]
    exact congrArg _ hfg

lemma min_degree (ha : 3 ≤ a) (hb : 3 ≤ b) (v : Fin a ⊕ Fin b) : 3 ≤ (K a b).degree v := by
  rcases v with i | j
  · rw [degree_inl]; exact hb
  · rw [degree_inr]; exact ha

/-- `K_{a,b}` has more spanning forests than its degree product when `b^a a^b < (a+1)^b`. -/
lemma violates (h : b ^ a * a ^ b < (a + 1) ^ b) :
    ∏ v, (K a b).degree v < numSpanningForests (K a b) := by
  rw [prod_degree]; exact h.trans_le card_le_numSpanningForests

/-- **The conjecture is false**: `K_{3,38}` has more than `∏ deg = 38³ · 3³⁸` spanning forests. -/
theorem not_conjecture : ¬ Conjecture := by
  intro h
  have := h _ (K 3 38) (min_degree le_rfl (by norm_num))
  have hv := violates (a := 3) (b := 38) (by norm_num)
  omega

lemma four_mul_cube_lt (a : ℕ) (ha : 1 ≤ a) : 4 * a ^ 3 < 16 ^ a := by
  induction a with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have := ih hn
      have h1 : (n + 1) ^ 3 ≤ 16 * n ^ 3 := by
        have : n + 1 ≤ 2 * n := by omega
        calc (n + 1) ^ 3 ≤ (2 * n) ^ 3 := Nat.pow_le_pow_left this 3
          _ = 8 * n ^ 3 := by ring
          _ ≤ 16 * n ^ 3 := by omega
      calc 4 * (n + 1) ^ 3 ≤ 16 * (4 * n ^ 3) := by omega
        _ < 16 * 16 ^ n := by omega
        _ = 16 ^ (n + 1) := by ring

/-- `(a+1)^a ≥ 2 a^a` (Bernoulli). -/
lemma two_mul_pow_le (a : ℕ) (ha : 1 ≤ a) : 2 * a ^ a ≤ (a + 1) ^ a := by
  · have ha' : (0 : ℚ) < a := by exact_mod_cast ha
    have hb := one_add_mul_le_pow (show (-2 : ℚ) ≤ 1 / a by
      have : (0 : ℚ) ≤ 1 / a := by positivity
      linarith) a
    have e1 : (1 : ℚ) + a * (1 / a) = 2 := by field_simp; ring
    have e2 : ((1 : ℚ) + 1 / a) ^ a * (a : ℚ) ^ a = ((a : ℚ) + 1) ^ a := by
      rw [← mul_pow]; congr 1; field_simp
    have : (2 : ℚ) * (a : ℚ) ^ a ≤ ((a : ℚ) + 1) ^ a := by
      rw [← e2, ← e1]
      exact mul_le_mul_of_nonneg_right hb (by positivity)
    exact_mod_cast this

/-- For `b = 4a³`: `b^a a^b < (a+1)^b`. -/
lemma key_ineq (a : ℕ) (ha : 1 ≤ a) :
    (4 * a ^ 3) ^ a * a ^ (4 * a ^ 3) < (a + 1) ^ (4 * a ^ 3) := by
  have hb : 4 * a ^ 3 = a * (4 * a ^ 2) := by ring
  have h1 : (4 * a ^ 3) ^ a < 2 ^ (4 * a ^ 2) := by
    calc (4 * a ^ 3) ^ a < (16 ^ a) ^ a :=
          Nat.pow_lt_pow_left (four_mul_cube_lt a ha) (by omega)
      _ = 2 ^ (4 * a ^ 2) := by rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]; ring_nf
  have h2 : 2 ^ (4 * a ^ 2) * a ^ (4 * a ^ 3) ≤ (a + 1) ^ (4 * a ^ 3) := by
    calc 2 ^ (4 * a ^ 2) * a ^ (4 * a ^ 3) = (2 * a ^ a) ^ (4 * a ^ 2) := by
          rw [mul_pow, ← pow_mul, hb]
      _ ≤ ((a + 1) ^ a) ^ (4 * a ^ 2) := Nat.pow_le_pow_left (two_mul_pow_le a ha) _
      _ = (a + 1) ^ (4 * a ^ 3) := by rw [← pow_mul, hb]
  have hpos : 0 < a ^ (4 * a ^ 3) := by positivity
  calc (4 * a ^ 3) ^ a * a ^ (4 * a ^ 3) < 2 ^ (4 * a ^ 2) * a ^ (4 * a ^ 3) :=
        Nat.mul_lt_mul_of_pos_right h1 hpos
    _ ≤ _ := h2

/-- **For every `a ≥ 3`** the complete bipartite graph `K_{a, 4a³}` is a counterexample. -/
theorem counterexample_for_every_a (ha : 3 ≤ a) :
    (∀ v, 3 ≤ (K a (4 * a ^ 3)).degree v) ∧
      ∏ v, (K a (4 * a ^ 3)).degree v < numSpanningForests (K a (4 * a ^ 3)) := by
  have hb : 3 ≤ 4 * a ^ 3 := by nlinarith [Nat.one_le_pow 3 a (by omega)]
  exact ⟨min_degree ha hb, violates (key_ineq a (by omega))⟩

end OpenProblemsLab.SpanningForests
