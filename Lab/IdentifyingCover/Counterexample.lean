import Mathlib

/-!
# The Henning–Yeo conjecture on identifying vertex covers is false

An **identifying vertex cover** of a graph `G` is a vertex set `T` that meets every edge, such that
distinct edges `e ≠ f` have distinct traces `e ∩ T ≠ f ∩ T`. The whole vertex set is one, so the
minimum size `τ_D(G)` is well defined.

M. A. Henning and A. Yeo (Electron. J. Combin. 19(4) (2012) P32, Conjecture 3) conjectured that every
finite graph of order `n`, size `m` and maximum degree `Δ` satisfies
`τ_D(G) ≤ (Δ(Δ − 1) n + 2 m) / (Δ² + 1)`. We formalize this as `HenningYeoConjecture`.

Y. Wang (arXiv:2608.19455, Theorem 3.1) disproved it with the graphs `H_{t,r}` (`t, r ≥ 2`): vertices
`a, b, x_1..x_t, c_1..c_r, d_1..d_r`; edges `a x_i`, `b x_i`, `a c_j`, `c_j d_j`, `d_j b`, and all
`d_i d_j`. Every two vertices are adjacent or have a common neighbour (diameter two), so at most one
vertex lies outside an identifying vertex cover, and `τ_D = n − 1`, while the bound is smaller by
`(t − 1)(r − 1) / (Δ² + 1)`.

Main results:
* `not_henningYeoConjecture`: the conjecture is false;
* `H_counterexample`: for all `t, r ≥ 2`, `H t r` is connected, has maximum degree `t + r`, and
  violates the bound;
* `exists_counterexample_of_maxDegree`: for every `Δ ≥ 4` there is a connected counterexample with
  maximum degree exactly `Δ`.
-/

namespace OpenProblemsLab.IdCover

open SimpleGraph Finset

section General

variable {V : Type*} [Fintype V]

/-- `T` is an identifying vertex cover of `G`: it meets every edge, and distinct edges have
distinct traces on `T`. -/
def IsIdCover (G : SimpleGraph V) (T : Finset V) : Prop :=
  (∀ e ∈ G.edgeSet, ∃ v ∈ e, v ∈ T) ∧
  ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, {v | v ∈ e ∧ v ∈ T} = {v | v ∈ f ∧ v ∈ T} → e = f

/-- The whole vertex set is an identifying vertex cover. -/
theorem isIdCover_univ (G : SimpleGraph V) : IsIdCover G Finset.univ := by
  refine ⟨fun e he => ?_, fun e _ f _ h => ?_⟩
  · induction e using Sym2.ind with
    | _ u w => exact ⟨u, Sym2.mem_mk_left u w, Finset.mem_univ u⟩
  · ext x
    have := congrArg (x ∈ ·) h
    simpa using this

/-- The identifying vertex cover number `τ_D(G)`. -/
noncomputable def idCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ T : Finset V, IsIdCover G T ∧ T.card = k}

theorem idCoverNumber_spec (G : SimpleGraph V) :
    ∃ T : Finset V, IsIdCover G T ∧ T.card = idCoverNumber G := by
  have h : ({k | ∃ T : Finset V, IsIdCover G T ∧ T.card = k} : Set ℕ).Nonempty :=
    ⟨_, Finset.univ, isIdCover_univ G, rfl⟩
  exact Nat.sInf_mem h

/-- If any two distinct vertices are adjacent or have a common neighbour, at most one vertex lies
outside an identifying vertex cover. -/
theorem card_le_card_add_one_of_diam_two [DecidableEq V] (G : SimpleGraph V)
    (hd : ∀ u v, u ≠ v → G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj v w)
    {T : Finset V} (hT : IsIdCover G T) : Fintype.card V ≤ T.card + 1 := by
  have h1 : (Finset.univ \ T).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro u hu v hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hu hv
    by_contra huv
    rcases hd u v huv with h | ⟨w, hu', hv'⟩
    · obtain ⟨x, hx, hxT⟩ := hT.1 s(u, v) h
      rcases Sym2.mem_iff.1 hx with rfl | rfl <;> contradiction
    · have heq := hT.2 s(u, w) hu' s(v, w) hv' (by
        ext x
        simp only [Set.mem_ofPred_eq, Sym2.mem_iff]
        constructor
        · rintro ⟨rfl | rfl, hx⟩
          · exact absurd hx hu
          · exact ⟨Or.inr rfl, hx⟩
        · rintro ⟨rfl | rfl, hx⟩
          · exact absurd hx hv
          · exact ⟨Or.inr rfl, hx⟩)
      rcases Sym2.eq_iff.1 heq with ⟨h, -⟩ | ⟨rfl, -⟩
      · exact huv h
      · exact G.irrefl hu'
  have h2 := Finset.card_sdiff_add_card_inter Finset.univ T
  rw [Finset.univ_inter, Finset.card_univ] at h2
  omega

/-- Removing one vertex from the whole vertex set leaves an identifying vertex cover. -/
theorem isIdCover_erase [DecidableEq V] (G : SimpleGraph V) (v : V) :
    IsIdCover G (Finset.univ.erase v) := by
  refine ⟨fun e he => ?_, fun e he f hf h => ?_⟩
  · induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeSet] at he
      by_cases hx : x = v
      · subst hx
        exact ⟨y, Sym2.mem_mk_right _ _, by simpa using (G.ne_of_adj he).symm⟩
      · exact ⟨x, Sym2.mem_mk_left _ _, by simpa using hx⟩
  have key : ∀ x, (x ∈ e ∧ x ≠ v) ↔ (x ∈ f ∧ x ≠ v) := fun x => by
    have := congrArg (x ∈ ·) h
    simpa using this
  have hv : ∀ e f : Sym2 V, f ∈ G.edgeSet →
      (∀ x, (x ∈ e ∧ x ≠ v) ↔ (x ∈ f ∧ x ≠ v)) → v ∈ e → v ∈ f := by
    intro e f hf k hve
    by_contra hvf
    induction f using Sym2.ind with
    | _ z w =>
    induction e using Sym2.ind with
    | _ a b =>
    rw [mem_edgeSet] at hf
    have hz := (k z).2 ⟨Sym2.mem_mk_left _ _, fun h => hvf (h ▸ Sym2.mem_mk_left _ _)⟩
    have hw := (k w).2 ⟨Sym2.mem_mk_right _ _, fun h => hvf (h ▸ Sym2.mem_mk_right _ _)⟩
    have hzw := G.ne_of_adj hf
    simp only [Sym2.mem_iff] at hz hw hve
    rcases hve with rfl | rfl <;> rcases hz with ⟨rfl | rfl, hz⟩ <;>
      rcases hw with ⟨rfl | rfl, hw⟩ <;> simp_all
  ext x
  by_cases hx : x = v
  · subst hx
    exact ⟨hv e f hf key, hv f e he (fun y => (key y).symm)⟩
  · simpa [hx] using key x

end General

/-- **Henning–Yeo conjecture** (2012, Conjecture 3): for every finite graph of order `n`, size `m`
and maximum degree `Δ`, `τ_D(G) ≤ (Δ(Δ − 1) n + 2 m) / (Δ² + 1)`. -/
def HenningYeoConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (idCoverNumber G : ℚ) ≤
      ((G.maxDegree : ℚ) * ((G.maxDegree : ℚ) - 1) * Fintype.card V + 2 * G.edgeFinset.card) /
        ((G.maxDegree : ℚ) ^ 2 + 1)

/-! ## Wang's graphs `H_{t,r}` -/

/-- Vertices: `inl false = a`, `inl true = b`, `inr (inl i) = x_i`, `inr (inr (inl j)) = c_j`,
`inr (inr (inr j)) = d_j`. -/
abbrev Vtx (t r : ℕ) := Bool ⊕ (Fin t ⊕ (Fin r ⊕ Fin r))

/-- Adjacency of `H_{t,r}` as a Boolean test. -/
def adjB {t r : ℕ} : Vtx t r → Vtx t r → Bool
  | .inl _, .inr (.inl _) => true                         -- a x_i, b x_i
  | .inr (.inl _), .inl _ => true
  | .inl false, .inr (.inr (.inl _)) => true              -- a c_j
  | .inr (.inr (.inl _)), .inl false => true
  | .inl true, .inr (.inr (.inr _)) => true               -- b d_j
  | .inr (.inr (.inr _)), .inl true => true
  | .inr (.inr (.inl i)), .inr (.inr (.inr j)) => decide (i = j)   -- c_j d_j
  | .inr (.inr (.inr j)), .inr (.inr (.inl i)) => decide (i = j)
  | .inr (.inr (.inr i)), .inr (.inr (.inr j)) => decide (i ≠ j)   -- d_i d_j
  | _, _ => false

/-- Wang's graph `H_{t,r}`. -/
def H (t r : ℕ) : SimpleGraph (Vtx t r) where
  Adj u v := adjB u v = true
  symm := ⟨fun u v h => by
    rcases u with (_ | _) | (_ | _ | _) <;> rcases v with (_ | _) | (_ | _ | _) <;>
      simp only [adjB, decide_eq_true_eq] at h ⊢ <;>
      first | trivial | exact h.symm⟩
  loopless := ⟨fun u h => by
    rcases u with (_ | _) | (_ | _ | _) <;> simp_all [adjB]⟩

instance (t r : ℕ) : DecidableRel (H t r).Adj :=
  fun u v => inferInstanceAs (Decidable (adjB u v = true))

theorem degree_eq_sum {t r : ℕ} (v : Vtx t r) :
    (H t r).degree v = ∑ w, if (H t r).Adj v w then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]

theorem degree_a (t r : ℕ) : (H t r).degree (.inl false) = t + r := by
  rw [degree_eq_sum]; simp only [Fintype.sum_sum_type, Fintype.sum_bool, H]; simp [adjB]

theorem degree_b (t r : ℕ) : (H t r).degree (.inl true) = t + r := by
  rw [degree_eq_sum]; simp only [Fintype.sum_sum_type, Fintype.sum_bool, H]; simp [adjB]

theorem degree_x {t r : ℕ} (i : Fin t) : (H t r).degree (.inr (.inl i)) = 2 := by
  rw [degree_eq_sum]; simp only [Fintype.sum_sum_type, Fintype.sum_bool, H]; simp [adjB]

theorem degree_c {t r : ℕ} (j : Fin r) : (H t r).degree (.inr (.inr (.inl j))) = 2 := by
  rw [degree_eq_sum]; simp only [Fintype.sum_sum_type, Fintype.sum_bool, H]; simp [adjB]

theorem sum_ne_one {r : ℕ} (j : Fin r) : (∑ x : Fin r, if j = x then 0 else 1) = r - 1 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    Finset.sum_congr rfl (g := fun _ => 1)
      (fun x hx => by simp [Ne.symm (Finset.ne_of_mem_erase hx)])]
  simp [Finset.card_erase_of_mem]

theorem degree_d {t r : ℕ} (j : Fin r) : (H t r).degree (.inr (.inr (.inr j))) = r + 1 := by
  rw [degree_eq_sum]; simp only [Fintype.sum_sum_type, Fintype.sum_bool, H]; simp [adjB]
  rw [sum_ne_one]; have := j.pos; omega

theorem card_vtx (t r : ℕ) : Fintype.card (Vtx t r) = t + 2 * r + 2 := by
  simp [Fintype.card_sum]; ring

theorem two_mul_card_edges (t r : ℕ) :
    2 * (H t r).edgeFinset.card = 4 * t + 5 * r + r ^ 2 := by
  rw [← sum_degrees_eq_twice_card_edges]
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, degree_a, degree_b, degree_x, degree_c,
    degree_d, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem maxDegree_H {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) : (H t r).maxDegree = t + r := by
  apply le_antisymm
  · apply maxDegree_le_of_forall_degree_le
    rintro ((_ | _) | (i | j | j))
    · rw [degree_a]
    · rw [degree_b]
    · rw [degree_x]; omega
    · rw [degree_c]; omega
    · rw [degree_d]; omega
  · exact degree_a t r ▸ (H t r).degree_le_maxDegree _

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- `H_{t,r}` has diameter at most two. -/
theorem diam_two {t r : ℕ} (ht : 1 ≤ t) (u v : Vtx t r) (huv : u ≠ v) :
    (H t r).Adj u v ∨ ∃ w, (H t r).Adj u w ∧ (H t r).Adj v w := by
  rcases u with (_ | _) | (i | i | i) <;> rcases v with (_ | _) | (j | j | j) <;>
  first
  | (left; simp_all [H, adjB]; done)
  | (right; refine ⟨.inl false, ?_, ?_⟩ <;> simp [H, adjB]; done)
  | (right; refine ⟨.inl true, ?_, ?_⟩ <;> simp [H, adjB]; done)
  | (right; refine ⟨.inr (.inl ⟨0, ht⟩), ?_, ?_⟩ <;> simp [H, adjB]; done)
  | (right; refine ⟨.inr (.inr (.inl i)), ?_, ?_⟩ <;> simp [H, adjB]; done)
  | (right; refine ⟨.inr (.inr (.inl j)), ?_, ?_⟩ <;> simp [H, adjB]; done)
  | (right; refine ⟨.inr (.inr (.inr i)), ?_, ?_⟩ <;> simp [H, adjB]; done)
  | (right; refine ⟨.inr (.inr (.inr j)), ?_, ?_⟩ <;> simp [H, adjB]; done)
  | (by_cases h : i = j
     · left; subst h; simp [H, adjB]
     · right
       first
       | (refine ⟨.inr (.inr (.inr i)), ?_, ?_⟩ <;> simp [H, adjB, h, Ne.symm h]; done)
       | (refine ⟨.inr (.inr (.inr j)), ?_, ?_⟩ <;> simp [H, adjB, h, Ne.symm h]; done))

theorem connected_H {t r : ℕ} (ht : 1 ≤ t) : (H t r).Connected := by
  refine ⟨fun u v => ?_⟩
  by_cases huv : u = v
  · exact huv ▸ Reachable.refl u
  rcases diam_two ht u v huv with h | ⟨w, hu, hv⟩
  · exact h.reachable
  · exact hu.reachable.trans hv.reachable.symm

/-- `τ_D(H_{t,r}) = t + 2r + 1 = n − 1`. -/
theorem idCoverNumber_H {t r : ℕ} (ht : 1 ≤ t) : idCoverNumber (H t r) = t + 2 * r + 1 := by
  apply le_antisymm
  · apply Nat.sInf_le
    refine ⟨Finset.univ.erase (.inl false), isIdCover_erase _ _, ?_⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_vtx]; rfl
  · obtain ⟨T, hT, hcard⟩ := idCoverNumber_spec (H t r)
    have h1 := card_le_card_add_one_of_diam_two (H t r) (diam_two ht) hT
    rw [card_vtx, hcard] at h1
    omega

/-- **Wang's Theorem 3.1.** For all `t, r ≥ 2`, `H_{t,r}` is connected, has maximum degree `t + r`,
and violates the Henning–Yeo bound. -/
theorem H_counterexample {t r : ℕ} (ht : 2 ≤ t) (hr : 2 ≤ r) :
    (H t r).Connected ∧ (H t r).maxDegree = t + r ∧
    ¬ (idCoverNumber (H t r) : ℚ) ≤
      (((H t r).maxDegree : ℚ) * (((H t r).maxDegree : ℚ) - 1) * Fintype.card (Vtx t r) +
          2 * (H t r).edgeFinset.card) / (((H t r).maxDegree : ℚ) ^ 2 + 1) := by
  refine ⟨connected_H (by omega), maxDegree_H (by omega) (by omega), ?_⟩
  obtain ⟨T, hT, hcard⟩ := idCoverNumber_spec (H t r)
  have h1 := card_le_card_add_one_of_diam_two (H t r) (diam_two (by omega)) hT
  rw [card_vtx, hcard] at h1
  have hτ : ((t : ℚ) + 2 * r + 1) ≤ idCoverNumber (H t r) := by exact_mod_cast (by omega : _)
  have hm : (2 * (H t r).edgeFinset.card : ℚ) = 4 * t + 5 * r + r ^ 2 := by
    exact_mod_cast two_mul_card_edges t r
  rw [maxDegree_H (by omega) (by omega), card_vtx, not_le, div_lt_iff₀ (by positivity)]
  push_cast
  have ht' : (2 : ℚ) ≤ t := by exact_mod_cast ht
  have hr' : (2 : ℚ) ≤ r := by exact_mod_cast hr
  have hpos : (0 : ℚ) < ((t : ℚ) - 1) * ((r : ℚ) - 1) := mul_pos (by linarith) (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hτ (by positivity : (0 : ℚ) ≤ ((t : ℚ) + r) ^ 2 + 1)
  nlinarith [hm, hmul, hpos]

/-- The Henning–Yeo conjecture is false. -/
theorem not_henningYeoConjecture : ¬ HenningYeoConjecture := fun h =>
  (H_counterexample (le_refl 2) (le_refl 2)).2.2 (h _ (H 2 2))

/-- For every `Δ ≥ 4` there is a connected counterexample with maximum degree exactly `Δ`
(Wang's Corollary 3.2, via `H_{2,Δ-2}`). -/
theorem exists_counterexample_of_maxDegree (Δ : ℕ) (hΔ : 4 ≤ Δ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.Connected ∧ G.maxDegree = Δ ∧
      ¬ (idCoverNumber G : ℚ) ≤
        ((G.maxDegree : ℚ) * ((G.maxDegree : ℚ) - 1) * Fintype.card V + 2 * G.edgeFinset.card) /
          ((G.maxDegree : ℚ) ^ 2 + 1) := by
  obtain ⟨h1, h2, h3⟩ := H_counterexample (t := 2) (r := Δ - 2) le_rfl (by omega)
  exact ⟨Vtx 2 (Δ - 2), inferInstance, H 2 (Δ - 2), inferInstance, h1, by rw [h2]; omega, h3⟩

end OpenProblemsLab.IdCover
