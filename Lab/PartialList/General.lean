import Lab.PartialList.Counterexample

/-!
# The Partial List Colouring Conjecture fails for every `k ≥ 3` (with `ℓ = k - 1`)

Noel (arXiv:2609.23291) disproved the Partial List Colouring Conjecture for `k = 3`, `ℓ = 2`.
His paper says the conjecture "remained open even in the first non-trivial case k = 3 and ℓ = 2";
no other case has been settled as far as we know. Here we generalise his construction to every
`k ≥ 3` with `ℓ = k - 1`. Write `m = k - 1 ≥ 2`.

## The graph `Gk m`

* `m` terminals `t₀, …, t_{m-1}`, pairwise non-adjacent (`Sum.inl t`);
* for every tuple `f : Fin m → Fin m`, a clique `K_{m+1}` with vertices `(f, 0), …, (f, m)`
  (`Sum.inr (f, i)`);
* the two *non-private* vertices `(f, 0)`, `(f, 1)` of every clique are joined to every terminal.

It has `n = m + (m + 1) m^m` vertices. For `m = 2` this is exactly Noel's graph.

## The bad `m`-lists

Colours are pairs `(i, a)` with `i, a < m` (encoded by `Nat.pair`):
`L(tᵢ) = {(i, a) : a < m}`, and every vertex of clique `f` gets `S_f = {(i, f i) : i < m}`.

## Results

* `partial_le`: every proper partial colouring from these lists colours at most
  `m · m^m + m - 1` vertices. Each clique has a common `m`-list, so it has at most `m` coloured
  vertices; if all `m` terminals are coloured, their colours are exactly `S_f` for one tuple `f`,
  and then neither non-private vertex of clique `f` can be coloured.
* `isKChoosable`: `Gk m` is `(m + 1)`-choosable. If two terminal lists meet, give those two
  terminals a common colour; otherwise count: a clique blocks a choice of terminal colours only
  if all `m` chosen colours lie in the `(m+1)`-list of its vertex `1`, which happens for at most
  `2` of the `(m+1)^m` choices, and `2 · m^m < (m+1)^m`. Then colour each clique greedily.
* `listChromaticNumber_Gk : (Gk m).listChromaticNumber = m + 1` (it contains `K_{m+1}`).
* `partial_violates`: `|S| · (m + 1) < n · m` for every partial colouring, i.e. fewer than
  `n ℓ / k` vertices can be coloured.
* `not_partialListColouringConjecture_general`: for every `k ≥ 3` there is a counterexample with
  list chromatic number `k` and `ℓ = k - 1`.
-/

namespace OpenProblemsLab.PartialList.General

open Finset SimpleGraph

variable (m : ℕ)

/-- Vertices: `m` terminals, and one `(m+1)`-clique per tuple `f : Fin m → Fin m`. -/
abbrev V := Fin m ⊕ ((Fin m → Fin m) × Fin (m + 1))

/-- Adjacency. -/
def gAdj : V m → V m → Prop
  | Sum.inl _, Sum.inl _ => False
  | Sum.inl _, Sum.inr p => p.2.val < 2
  | Sum.inr p, Sum.inl _ => p.2.val < 2
  | Sum.inr p, Sum.inr q => p.1 = q.1 ∧ p.2 ≠ q.2

/-- **The graph** `Gk m`: Noel's construction for `k = m + 1` colours. -/
def Gk : SimpleGraph (V m) where
  Adj := gAdj m
  symm := by
    refine ⟨?_⟩
    rintro (a | ⟨f, i⟩) (b | ⟨g, j⟩) h <;> simp only [gAdj] at h ⊢
    · exact h
    · exact h
    · exact ⟨h.1.symm, fun e => h.2 e.symm⟩
  loopless := by
    refine ⟨?_⟩
    rintro (a | ⟨f, i⟩) h <;> simp only [gAdj] at h
    exact h.2 rfl

variable {m}

theorem adj_term {t : Fin m} {f : Fin m → Fin m} {i : Fin (m + 1)} (hi : i.val < 2) :
    (Gk m).Adj (Sum.inl t) (Sum.inr (f, i)) := hi

theorem adj_clique {f : Fin m → Fin m} {i j : Fin (m + 1)} (h : i ≠ j) :
    (Gk m).Adj (Sum.inr (f, i)) (Sum.inr (f, j)) := ⟨rfl, h⟩

/-! ### The bad lists -/

/-- The bad `m`-lists. -/
def Lb : V m → Finset ℕ
  | Sum.inl t => univ.image (fun a : Fin m => Nat.pair t a)
  | Sum.inr p => univ.image (fun t : Fin m => Nat.pair t (p.1 t))

theorem Lb_card (v : V m) : (Lb v).card = m := by
  rcases v with t | ⟨f, i⟩
  · simp only [Lb]
    rw [card_image_of_injective _ (fun a b h => Fin.ext (Nat.pair_eq_pair.1 h).2), card_univ,
      Fintype.card_fin]
  · simp only [Lb]
    rw [card_image_of_injective _ (fun a b h => Fin.ext (Nat.pair_eq_pair.1 h).1), card_univ,
      Fintype.card_fin]

/-! ### At most `m · m^m + m - 1` vertices can be coloured -/

section Partial

variable {S : Finset (V m)} {c : V m → ℕ}

/-- Coloured vertices of clique `f`. -/
def cl (S : Finset (V m)) (f : Fin m → Fin m) : Finset (Fin (m + 1)) :=
  univ.filter (fun i => Sum.inr (f, i) ∈ S)

/-- Coloured terminals. -/
def tm (S : Finset (V m)) : Finset (Fin m) := univ.filter (fun t => Sum.inl t ∈ S)

theorem card_split (S : Finset (V m)) : S.card = (tm S).card + ∑ f, (cl S f).card := by
  have h1 : S.card = ∑ v : V m, if v ∈ S then 1 else 0 := by
    rw [← card_filter]
    congr 1
    ext v
    simp
  rw [h1, Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  · rw [tm, card_filter]
  · apply sum_congr rfl
    intro f _
    rw [cl, card_filter]

variable (hL : ∀ v ∈ S, c v ∈ Lb v) (hP : ∀ u ∈ S, ∀ v ∈ S, (Gk m).Adj u v → c u ≠ c v)
include hL hP

/-- A clique has at most `m` coloured vertices: they get distinct colours from one `m`-list. -/
theorem cl_card_le (f : Fin m → Fin m) : (cl S f).card ≤ m := by
  refine le_trans ?_ (Lb_card (m := m) (Sum.inr (f, 0))).le
  apply card_le_card_of_injOn (fun i => c (Sum.inr (f, i)))
  · intro i hi
    have hi' : Sum.inr (f, i) ∈ S := (mem_filter.1 hi).2
    have := hL _ hi'
    simpa [Lb] using this
  · intro i hi j hj hij
    by_contra hne
    exact hP _ (mem_filter.1 hi).2 _ (mem_filter.1 hj).2 (adj_clique hne) hij

/-- If every terminal is coloured, some clique has no coloured non-private vertex. -/
theorem exists_blocked (hT : tm S = univ) :
    ∃ f : Fin m → Fin m, (cl S f).card ≤ m - 1 := by
  rcases Nat.eq_zero_or_pos m with h0 | hm0
  · refine ⟨fun t => t, ?_⟩
    have := cl_card_le hL hP (fun t => t)
    omega
  have hmem : ∀ t : Fin m, Sum.inl t ∈ S := fun t => by
    have : t ∈ tm S := by rw [hT]; exact mem_univ t
    exact (mem_filter.1 this).2
  have hex : ∀ t : Fin m, ∃ a : Fin m, c (Sum.inl t) = Nat.pair t a := by
    intro t
    have := hL _ (hmem t)
    simp only [Lb, mem_image, mem_univ, true_and] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha.symm⟩
  choose f hf using hex
  refine ⟨f, ?_⟩
  -- the non-private vertices of clique `f` are uncoloured
  have hnp : ∀ i : Fin (m + 1), i.val < 2 → i ∉ cl S f := by
    intro i hi hiS
    have hiS' : Sum.inr (f, i) ∈ S := (mem_filter.1 hiS).2
    have := hL _ hiS'
    simp only [Lb, mem_image, mem_univ, true_and] at this
    obtain ⟨t, ht⟩ := this
    exact hP _ (hmem t) _ hiS' (adj_term hi) (by rw [hf t, ht])
  have hsub : cl S f ⊆ univ.filter (fun i : Fin (m + 1) => ¬ i.val < 2) := by
    intro i hi
    rw [mem_filter]
    exact ⟨mem_univ i, fun h => hnp i h hi⟩
  have h2 : 2 ≤ (univ.filter (fun i : Fin (m + 1) => i.val < 2)).card := by
    have hpair : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (m + 1))) ⊆
        univ.filter (fun i : Fin (m + 1) => i.val < 2) := by
      intro i hi
      simp only [mem_insert, mem_singleton] at hi
      rw [mem_filter]
      rcases hi with rfl | rfl <;> exact ⟨mem_univ _, by simp⟩
    have := card_le_card hpair
    rw [card_pair (by simp [Fin.ext_iff])] at this
    exact this
  have htot := card_filter_add_card_filter_not (s := (univ : Finset (Fin (m + 1))))
    (fun i : Fin (m + 1) => i.val < 2)
  rw [card_univ, Fintype.card_fin] at htot
  have := card_le_card hsub
  omega

/-- **At most `m · m^m + m - 1` vertices** can be coloured from the bad lists. -/
theorem partial_le (hm : 1 ≤ m) : S.card ≤ m * m ^ m + m - 1 := by
  rw [card_split]
  have hcl : ∀ f, (cl S f).card ≤ m := cl_card_le hL hP
  have hcard : (univ : Finset (Fin m → Fin m)).card = m ^ m := by
    rw [card_univ, Fintype.card_fun, Fintype.card_fin]
  by_cases hT : tm S = univ
  · obtain ⟨f, hf⟩ := exists_blocked hL hP hT
    have htm : (tm S).card = m := by rw [hT, card_univ, Fintype.card_fin]
    rw [← add_sum_erase _ _ (mem_univ f)]
    have hrest : ∑ g ∈ univ.erase f, (cl S g).card ≤ (m ^ m - 1) * m := by
      calc ∑ g ∈ univ.erase f, (cl S g).card ≤ ∑ _g ∈ univ.erase f, m := sum_le_sum fun g _ => hcl g
        _ = (m ^ m - 1) * m := by rw [sum_const, card_erase_of_mem (mem_univ f), hcard,
            smul_eq_mul]
    have hpos : 1 ≤ m ^ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp
      · exact Nat.one_le_pow _ _ h
    obtain ⟨q, hq⟩ : ∃ q, m ^ m = q + 1 := ⟨m ^ m - 1, by omega⟩
    rw [hq, Nat.add_sub_cancel] at hrest
    rw [htm, hq]
    have e : m * (q + 1) = q * m + m := by ring
    rw [e]
    generalize q * m = Z at hrest ⊢
    generalize ∑ g ∈ univ.erase f, (cl S g).card = X at hrest ⊢
    omega
  · have htm : (tm S).card ≤ m - 1 := by
      obtain ⟨t, ht⟩ : ∃ t, t ∉ tm S := by
        by_contra h
        push Not at h
        exact hT (eq_univ_of_forall h)
      have hsub : tm S ⊆ univ.erase t := fun x hx =>
        mem_erase.2 ⟨fun e => ht (e ▸ hx), mem_univ x⟩
      have := card_le_card hsub
      rw [card_erase_of_mem (mem_univ t), card_univ, Fintype.card_fin] at this
      exact this
    have hsum : ∑ f, (cl S f).card ≤ m * m ^ m := by
      calc ∑ f, (cl S f).card ≤ ∑ _f : Fin m → Fin m, m := sum_le_sum fun g _ => hcl g
        _ = m * m ^ m := by rw [sum_const, hcard, smul_eq_mul, mul_comm]
    omega

end Partial

/-! ### `Gk m` is `(m + 1)`-choosable -/

section Choosable

/-- **Greedy colouring of a clique**: if the `i`-th list has more than `i` colours, the lists
have a system of distinct representatives. -/
theorem greedy : ∀ (n : ℕ) (Λ : Fin n → Finset ℕ), (∀ i, i.val < (Λ i).card) →
    ∃ g : Fin n → ℕ, (∀ i, g i ∈ Λ i) ∧ Function.Injective g
  | 0, _, _ => ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | n + 1, Λ, h => by
    obtain ⟨g, hg, hinj⟩ := greedy n (fun i => Λ i.castSucc) (fun i => h i.castSucc)
    obtain ⟨x, hx, hx'⟩ := exists_mem_notMem (s := Λ (Fin.last n)) (t := univ.image g) (by
      calc (univ.image g).card ≤ (univ : Finset (Fin n)).card := card_image_le
        _ = n := by rw [card_univ, Fintype.card_fin]
        _ < (Λ (Fin.last n)).card := h (Fin.last n))
    refine ⟨Fin.snoc (α := fun _ => ℕ) g x, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using hg j
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rfl
        | cast j =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact absurd (mem_image.2 ⟨j, mem_univ j, hij.symm⟩) hx'
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact absurd (mem_image.2 ⟨i, mem_univ i, hij⟩) hx'
        | cast j =>
          simp only [Fin.snoc_castSucc] at hij
          rw [hinj hij]

/-- Nonneg integers `x₀, …, x_{m-1}` with sum at most `m + 1` have product at most `2`. -/
theorem prod_le_two (x : Fin m → ℕ) (h : ∑ i, x i ≤ m + 1) : ∏ i, x i ≤ 2 := by
  by_cases h0 : ∃ i, x i = 0
  · obtain ⟨i, hi⟩ := h0
    rw [prod_eq_zero (mem_univ i) hi]
    omega
  · push Not at h0
    have hpos : ∀ i, 1 ≤ x i := fun i => Nat.one_le_iff_ne_zero.2 (h0 i)
    have hle : ∀ i, x i ≤ 2 ^ (x i - 1) := by
      intro i
      obtain ⟨y, hy⟩ : ∃ y, x i = y + 1 := ⟨x i - 1, by have := hpos i; omega⟩
      rw [hy, Nat.add_sub_cancel]
      exact Nat.lt_two_pow_self
    have hsum : ∑ i, (x i - 1) + m = ∑ i, x i := by
      have : ∑ i : Fin m, (x i - 1 + 1) = ∑ i, x i :=
        sum_congr rfl fun i _ => Nat.sub_add_cancel (hpos i)
      rw [← this, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    calc ∏ i, x i ≤ ∏ i, 2 ^ (x i - 1) := prod_le_prod (fun i _ => Nat.zero_le _) fun i _ => hle i
      _ = 2 ^ (∑ i, (x i - 1)) := prod_pow_eq_pow_sum _ _ _
      _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := by norm_num

/-- `a^(n+1) + n a^n ≤ a (a+1)^n`. -/
theorem bern (a : ℕ) : ∀ n : ℕ, a ^ (n + 1) + n * a ^ n ≤ a * (a + 1) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := bern a n
    calc a ^ (n + 1 + 1) + (n + 1) * a ^ (n + 1)
        ≤ (a + 1) * (a ^ (n + 1) + n * a ^ n) := by
          have : (a + 1) * (a ^ (n + 1) + n * a ^ n) =
              a ^ (n + 1 + 1) + (n + 1) * a ^ (n + 1) + n * a ^ n := by ring
          rw [this]; omega
      _ ≤ (a + 1) * (a * (a + 1) ^ n) := Nat.mul_le_mul_left _ ih
      _ = a * (a + 1) ^ (n + 1) := by ring

/-- `2 m^m < (m+1)^m` for `m ≥ 2`. -/
theorem two_pow_lt (hm : 2 ≤ m) : 2 * m ^ m < (m + 1) ^ m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hb := bern (n + 1) n
  have hn : 1 ≤ n := by omega
  have hp : 1 ≤ n * (n + 1) ^ n := Nat.mul_le_mul hn (Nat.one_le_pow _ _ (by omega))
  -- multiply the goal by `n + 1`
  have key : (n + 1) * (2 * (n + 1) ^ (n + 1)) < (n + 1) * (n + 1 + 1) ^ (n + 1) := by
    calc (n + 1) * (2 * (n + 1) ^ (n + 1))
        < (n + 1 + 1) * ((n + 1) ^ (n + 1) + n * (n + 1) ^ n) := by
          have e1 : (n + 1 + 1) * ((n + 1) ^ (n + 1) + n * (n + 1) ^ n) =
              (n + 1) * (2 * (n + 1) ^ (n + 1)) + n * (n + 1) ^ n := by ring
          rw [e1]; omega
      _ ≤ (n + 1 + 1) * ((n + 1) * (n + 1 + 1) ^ n) := Nat.mul_le_mul_left _ hb
      _ = (n + 1) * (n + 1 + 1) ^ (n + 1) := by ring
  exact Nat.lt_of_mul_lt_mul_left key

/-- **Choosing the terminal colours.** There are colours `ct t ∈ L(t)` such that, writing `C`
for the set of chosen colours, every clique's vertex `1` keeps at least 2 colours outside `C`
(equivalently `|L(f,1) ∩ C| ≤ m - 1`). -/
theorem terminal_choice (L : V m → Finset ℕ) (hL : ∀ v, (L v).card = m + 1) (hm : 2 ≤ m) :
    ∃ ct : Fin m → ℕ, (∀ t, ct t ∈ L (Sum.inl t)) ∧
      ∀ f : Fin m → Fin m, (L (Sum.inr (f, 1)) ∩ univ.image ct).card ≤ m - 1 := by
  have hne : ∀ v, (L v).Nonempty := fun v => card_pos.1 (by rw [hL v]; omega)
  by_cases hmeet : ∃ t₁ t₂ : Fin m, t₁ ≠ t₂ ∧ (L (Sum.inl t₁) ∩ L (Sum.inl t₂)).Nonempty
  · obtain ⟨t₁, t₂, h12, x, hx⟩ := hmeet
    rw [mem_inter] at hx
    classical
    let ct : Fin m → ℕ := fun t =>
      if t = t₁ ∨ t = t₂ then x else (hne (Sum.inl t)).choose
    refine ⟨ct, ?_, ?_⟩
    · intro t
      simp only [ct]
      split_ifs with h
      · rcases h with rfl | rfl
        · exact hx.1
        · exact hx.2
      · exact (hne (Sum.inl t)).choose_spec
    · intro f
      have hsub : univ.image ct ⊆ (univ.erase t₁).image ct := by
        intro y hy
        obtain ⟨t, _, rfl⟩ := mem_image.1 hy
        by_cases ht : t = t₁
        · refine mem_image.2 ⟨t₂, mem_erase.2 ⟨fun e => h12 e.symm, mem_univ _⟩, ?_⟩
          simp [ct, ht]
        · exact mem_image.2 ⟨t, mem_erase.2 ⟨ht, mem_univ _⟩, rfl⟩
      calc (L (Sum.inr (f, 1)) ∩ univ.image ct).card ≤ (univ.image ct).card :=
            card_le_card inter_subset_right
        _ ≤ ((univ.erase t₁).image ct).card := card_le_card hsub
        _ ≤ (univ.erase t₁).card := card_image_le
        _ = m - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  · push Not at hmeet
    have hdisj : ∀ t₁ t₂ : Fin m, t₁ ≠ t₂ → Disjoint (L (Sum.inl t₁)) (L (Sum.inl t₂)) :=
      fun t₁ t₂ h => disjoint_iff_inter_eq_empty.2 (hmeet t₁ t₂ h)
    classical
    set A : Fin m → Finset ℕ := fun t => L (Sum.inl t) with hA
    set bad := (univ : Finset (Fin m → Fin m)).biUnion
      (fun f => Fintype.piFinset (fun t => A t ∩ L (Sum.inr (f, 1)))) with hbad
    have hblock : ∀ f : Fin m → Fin m,
        (Fintype.piFinset (fun t => A t ∩ L (Sum.inr (f, 1)))).card ≤ 2 := by
      intro f
      rw [Fintype.card_piFinset]
      apply prod_le_two
      have hpd : ((univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
          (fun t => A t ∩ L (Sum.inr (f, 1))) := by
        intro t₁ _ t₂ _ h
        exact Disjoint.mono inter_subset_left inter_subset_left (hdisj t₁ t₂ h)
      rw [← card_biUnion hpd]
      refine le_trans ?_ (hL (Sum.inr (f, 1))).le
      apply card_le_card
      intro y hy
      obtain ⟨t, _, hy⟩ := mem_biUnion.1 hy
      exact (mem_inter.1 hy).2
    have hbadcard : bad.card ≤ 2 * m ^ m := by
      calc bad.card ≤ ∑ f : Fin m → Fin m,
            (Fintype.piFinset (fun t => A t ∩ L (Sum.inr (f, 1)))).card := card_biUnion_le
        _ ≤ ∑ _f : Fin m → Fin m, 2 := sum_le_sum fun f _ => hblock f
        _ = 2 * m ^ m := by
            rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul, mul_comm]
    have hall : (Fintype.piFinset A).card = (m + 1) ^ m := by
      rw [Fintype.card_piFinset]
      simp [hA, hL]
    obtain ⟨ct, hct, hnot⟩ := exists_mem_notMem_of_card_lt_card
      (show bad.card < (Fintype.piFinset A).card by
        rw [hall]; exact lt_of_le_of_lt hbadcard (two_pow_lt hm))
    rw [Fintype.mem_piFinset] at hct
    refine ⟨ct, hct, fun f => ?_⟩
    -- some chosen colour is missing from `L (f, 1)`
    have hmiss : ∃ t, ct t ∉ L (Sum.inr (f, 1)) := by
      by_contra hc
      push Not at hc
      apply hnot
      rw [hbad, mem_biUnion]
      exact ⟨f, mem_univ f, Fintype.mem_piFinset.2 fun t => mem_inter.2 ⟨hct t, hc t⟩⟩
    obtain ⟨t, ht⟩ := hmiss
    have hlt : (L (Sum.inr (f, 1)) ∩ univ.image ct).card < (univ.image ct).card := by
      apply card_lt_card
      refine ⟨inter_subset_right, fun h => ht ?_⟩
      exact (mem_inter.1 (h (mem_image.2 ⟨t, mem_univ t, rfl⟩))).1
    have : (univ.image ct).card ≤ m := by
      calc (univ.image ct).card ≤ (univ : Finset (Fin m)).card := card_image_le
        _ = m := by rw [card_univ, Fintype.card_fin]
    omega

/-- **`Gk m` is `(m + 1)`-choosable** for `m ≥ 2`. -/
theorem isKChoosable (hm : 2 ≤ m) : (Gk m).IsKChoosable (m + 1) := by
  intro L hL
  obtain ⟨ct, hct, hgood⟩ := terminal_choice L hL hm
  classical
  set C := univ.image ct with hC
  have hCcard : C.card ≤ m := by
    calc C.card ≤ (univ : Finset (Fin m)).card := card_image_le
      _ = m := by rw [card_univ, Fintype.card_fin]
  -- lists for the clique `f`: non-private vertices avoid `C`
  let Λ : (Fin m → Fin m) → Fin (m + 1) → Finset ℕ := fun f i =>
    if i.val < 2 then L (Sum.inr (f, i)) \ C else L (Sum.inr (f, i))
  have hΛ : ∀ f i, i.val < (Λ f i).card := by
    intro f i
    simp only [Λ]
    split_ifs with hi
    · have hsd := card_sdiff_add_card_inter (L (Sum.inr (f, i))) C
      rw [hL] at hsd
      by_cases h0 : i.val = 0
      · have : (L (Sum.inr (f, i)) ∩ C).card ≤ m :=
          (card_le_card inter_subset_right).trans hCcard
        omega
      · have hi1 : i = 1 := by
          ext
          simp only [Fin.val_one']
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        have := hgood f
        rw [← hi1] at this
        omega
    · rw [hL]; exact i.isLt
  choose g hg hinj using fun f => greedy (m + 1) (Λ f) (hΛ f)
  let col : V m → ℕ := fun v => match v with
    | Sum.inl t => ct t
    | Sum.inr p => g p.1 p.2
  refine ⟨Coloring.mk col ?_, ?_⟩
  · rintro (a | ⟨f, i⟩) (b | ⟨f', j⟩) h
    · exact absurd h (by simp [Gk, gAdj])
    · -- terminal `a`, clique vertex `(f', j)` with `j` non-private
      have hj : j.val < 2 := h
      have hm := hg f' j
      simp only [Λ, hj, if_true, mem_sdiff] at hm
      intro e
      apply hm.2
      rw [hC]
      exact mem_image.2 ⟨a, mem_univ a, e⟩
    · have hi : i.val < 2 := h
      have hm := hg f i
      simp only [Λ, hi, if_true, mem_sdiff] at hm
      intro e
      apply hm.2
      rw [hC]
      exact mem_image.2 ⟨b, mem_univ b, e.symm⟩
    · obtain ⟨hf, hij⟩ := h
      simp only at hf
      subst hf
      intro e
      exact hij (hinj f e)
  · rintro (t | ⟨f, i⟩)
    · exact hct t
    · have hm := hg f i
      show g f i ∈ L (Sum.inr (f, i))
      simp only [Λ] at hm
      split_ifs at hm
      · exact (mem_sdiff.1 hm).1
      · exact hm

end Choosable

/-! ### The list chromatic number is `m + 1` -/

/-- `Gk m` contains the clique `K_{m+1}`, so it is not `k`-choosable for `k ≤ m`. -/
theorem not_isKChoosable_of_le {k : ℕ} (hk : k ≤ m) : ¬ (Gk m).IsKChoosable k := by
  intro h
  obtain ⟨C⟩ := (IsKChoosable.colorable h).mono hk
  let f0 : Fin m → Fin m := fun t => t
  let φ : Fin (m + 1) → Fin m := fun i => C (Sum.inr (f0, i))
  have hφ : Function.Injective φ := by
    intro i j hij
    by_contra hne
    exact C.valid (adj_clique (f := f0) hne) hij
  have := Fintype.card_le_of_injective φ hφ
  simp at this

theorem listChromaticNumber_Gk (hm : 2 ≤ m) : (Gk m).listChromaticNumber = m + 1 := by
  apply le_antisymm (Nat.sInf_le (isKChoosable hm))
  apply le_csInf ⟨m + 1, isKChoosable hm⟩
  intro k hk
  by_contra h
  exact not_isKChoosable_of_le (by omega) hk

/-! ### The disproof for every `k ≥ 3` -/

theorem card_V : Fintype.card (V m) = m + m ^ m * (m + 1) := by
  simp [Fintype.card_sum, Fintype.card_prod]

/-- **Fewer than `n ℓ / k` vertices can be coloured**: `|S| · (m + 1) < n · m`. -/
theorem partial_violates (hm : 2 ≤ m) {S : Finset (V m)} {c : V m → ℕ}
    (hL : ∀ v ∈ S, c v ∈ Lb v) (hP : ∀ u ∈ S, ∀ v ∈ S, (Gk m).Adj u v → c u ≠ c v) :
    S.card * (m + 1) < Fintype.card (V m) * m := by
  have h := partial_le hL hP (by omega)
  rw [card_V]
  set P := m ^ m
  have hS : S.card * (m + 1) ≤ (m * P + m - 1) * (m + 1) := Nat.mul_le_mul_right _ h
  have e1 : (m * P + m - 1) * (m + 1) + 1 = (m * P) * (m + 1) + m * m := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have : (j + 1) * P + (j + 1) - 1 = (j + 1) * P + j := by omega
    rw [this]
    ring
  have e2 : (m + P * (m + 1)) * m = (m * P) * (m + 1) + m * m := by ring
  rw [e2]
  omega

/-- **The Partial List Colouring Conjecture fails for every `k ≥ 3`**, with `ℓ = k - 1`: there is
a finite graph with list chromatic number `k` and a `(k-1)`-list assignment from which fewer than
`n (k-1) / k` vertices can be properly coloured. -/
theorem not_partialListColouringConjecture_general (k : ℕ) (hk : 3 ≤ k) :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W), H.listChromaticNumber = k ∧
      ∃ L : W → Finset ℕ, (∀ v, (L v).card = k - 1) ∧
        ∀ S : Finset W, ∀ c : W → ℕ, (∀ v ∈ S, c v ∈ L v) →
          (∀ u ∈ S, ∀ v ∈ S, H.Adj u v → c u ≠ c v) →
            S.card * k < Fintype.card W * (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  refine ⟨V m, inferInstance, Gk m, listChromaticNumber_Gk hm, Lb, fun v => ?_,
    fun S c hL hP => ?_⟩
  · rw [Lb_card]; rfl
  · simpa using partial_violates hm hL hP

/-- In particular `¬ PartialListColouringConjecture`, again, from any `k ≥ 3`. -/
theorem not_conjecture_of (k : ℕ) (hk : 3 ≤ k) : ¬ PartialListColouringConjecture := by
  intro h
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  obtain ⟨S, c, hL, hP, hcard⟩ := h (V m) (Gk m) m (by omega)
    (by rw [listChromaticNumber_Gk hm]; omega) Lb Lb_card
  have := partial_violates hm hL hP
  rw [listChromaticNumber_Gk hm] at hcard
  omega

end OpenProblemsLab.PartialList.General
