import Mathlib

/-!
# Bipanchromatic colourings: the sunflower counterexamples

A *panchromatic `k`-colouring* of a hypergraph `H = (V, E)` is a map `c : V → Fin k` such that
every hyperedge contains a vertex of every colour; `χ_P(H)` is the largest such `k`. A colour is
*unique* if it is used on exactly one vertex; `α_k(H)` is the least number of vertices of unique
colour over all panchromatic `k`-colourings, and `α(H) = α_{χ_P}(H)`. A panchromatic colouring is
*bipanchromatic* if no colour is unique; `χ_B(H)` is the largest `k` with a bipanchromatic
`k`-colouring.

Lalou, Mbarek, Skender and Togni (Discrete Appl. Math. 2026, Conjecture 1) conjectured `χ_B = χ_P - ⌈α/2⌉` for every
hypergraph (merging the unique colours of an optimal panchromatic colouring in pairs is optimal).
The same authors disproved it (arXiv:2610.08042); Novaković and Jojić (arXiv:2610.27133, Theorem 1) give the *sunflowers*
`S_n`: vertices `s_1,…,s_n, p_1,…,p_n` and hyperedges `e_i = {s_1,…,s_n, p_i}`. For `n ≥ 3`,
`χ_P = n + 1`, `α = n`, `χ_B = n`, so `χ_B` exceeds the conjectured value by `⌈n/2⌉ - 1 ≥ 1`.
`S_3` (six vertices, three hyperedges) is the smallest counterexample.

This file proves the sunflower theorem for every `n ≥ 3` (`sunflower_parameters`) and deduces
that the conjecture fails, even after adding any constant (`not_conjecture`, `excess_unbounded`).
-/

namespace OpenProblemsLab.Bipanchromatic

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `c : V → Fin k` is a panchromatic `k`-colouring of the hypergraph with hyperedges `E`. -/
def IsPanchromatic (E : Finset (Finset V)) {k : ℕ} (c : V → Fin k) : Prop :=
  ∀ e ∈ E, ∀ i : Fin k, ∃ v ∈ e, c v = i

/-- The vertices whose colour is used nowhere else. -/
def uniqueVerts {k : ℕ} (c : V → Fin k) : Finset V :=
  univ.filter fun v => ∀ w, c w = c v → w = v

/-- The panchromatic number `χ_P`. -/
noncomputable def chiP (E : Finset (Finset V)) : ℕ :=
  sSup {k | ∃ c : V → Fin k, IsPanchromatic E c}

/-- `α_k`: the least number of vertices of unique colour in a panchromatic `k`-colouring. -/
noncomputable def alphaK (E : Finset (Finset V)) (k : ℕ) : ℕ :=
  sInf {m | ∃ c : V → Fin k, IsPanchromatic E c ∧ (uniqueVerts c).card = m}

/-- `α = α_{χ_P}`. -/
noncomputable def alpha (E : Finset (Finset V)) : ℕ := alphaK E (chiP E)

/-- The bipanchromatic number `χ_B`. -/
noncomputable def chiB (E : Finset (Finset V)) : ℕ :=
  sSup {k | ∃ c : V → Fin k, IsPanchromatic E c ∧ uniqueVerts c = ∅}

/-- **Conjecture (Lalou et al.)**: `χ_B = χ_P - ⌈α/2⌉` for every finite hypergraph. We even
restrict to hypergraphs with at least two vertices and at least one hyperedge, all of size `≥ 2`
(written `⌈α/2⌉ = (α + 1)/2`). -/
def Conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (E : Finset (Finset V)),
    2 ≤ Fintype.card V → E.Nonempty → (∀ e ∈ E, 2 ≤ e.card) →
      chiB E = chiP E - (alpha E + 1) / 2

/-! ### The sunflower `S_n` -/

/-- Vertices of `S_n`: `inl i = s_i`, `inr i = p_i`. -/
abbrev SV (n : ℕ) := Fin n ⊕ Fin n

/-- The hyperedge `e_i = S ∪ {p_i}`. -/
def petal (n : ℕ) (i : Fin n) : Finset (SV n) := univ.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ {Sum.inr i}

/-- The hyperedges of `S_n`. -/
def sunflower (n : ℕ) : Finset (Finset (SV n)) := univ.image (petal n)

lemma mem_petal {n : ℕ} {i : Fin n} {v : SV n} : v ∈ petal n i ↔ (v.isLeft ∨ v = Sum.inr i) := by
  rcases v with j | j <;> simp [petal]

lemma card_petal (n : ℕ) (i : Fin n) : (petal n i).card = n + 1 := by
  rw [petal, card_union_of_disjoint]
  · simp
  · simp [Finset.disjoint_left]

lemma card_SV (n : ℕ) : Fintype.card (SV n) = 2 * n := by simp; ring

variable {n : ℕ}

/-- Any panchromatic `k`-colouring of `S_n` (`n ≥ 1`) has `k ≤ n + 1`. -/
lemma le_of_pan (hn : 1 ≤ n) {k : ℕ} {c : SV n → Fin k} (hc : IsPanchromatic (sunflower n) c) :
    k ≤ n + 1 := by
  have he : petal n ⟨0, hn⟩ ∈ sunflower n := mem_image_of_mem _ (mem_univ _)
  have hsurj : (univ : Finset (Fin k)) ⊆ (petal n ⟨0, hn⟩).image c := by
    intro i _
    obtain ⟨v, hv, rfl⟩ := hc _ he i
    exact mem_image_of_mem _ hv
  have := card_le_card hsurj
  rw [card_univ, Fintype.card_fin] at this
  exact this.trans (card_image_le.trans (card_petal n _).le)

/-- The panchromatic `(n+1)`-colouring `s_i ↦ i`, `p_i ↦ n`. -/
def panColouring (n : ℕ) : SV n → Fin (n + 1)
  | Sum.inl i => i.castSucc
  | Sum.inr _ => Fin.last n

lemma panColouring_pan : IsPanchromatic (sunflower n) (panColouring n) := by
  intro e he j
  obtain ⟨i, -, rfl⟩ := mem_image.1 he
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · exact ⟨Sum.inl j', mem_petal.2 (Or.inl rfl), rfl⟩
  · exact ⟨Sum.inr i, mem_petal.2 (Or.inr rfl), rfl⟩

/-- A panchromatic `(n+1)`-colouring is injective on every hyperedge. -/
lemma injOn_petal {c : SV n → Fin (n + 1)} (hc : IsPanchromatic (sunflower n) c) (i : Fin n) :
    Set.InjOn c (petal n i) := by
  have he : petal n i ∈ sunflower n := mem_image_of_mem _ (mem_univ _)
  have hsurj : (univ : Finset (Fin (n + 1))) ⊆ (petal n i).image c := by
    intro j _
    obtain ⟨v, hv, rfl⟩ := hc _ he j
    exact mem_image_of_mem _ hv
  have h1 := card_le_card hsurj
  rw [card_univ, Fintype.card_fin] at h1
  have h2 : ((petal n i).image c).card = (petal n i).card :=
    le_antisymm card_image_le (by rw [card_petal]; exact h1)
  exact card_image_iff.1 h2

/-- For `n ≥ 2`, the vertices of unique colour of a panchromatic `(n+1)`-colouring of `S_n` are
exactly `s_1, …, s_n`. -/
lemma uniqueVerts_eq (hn : 2 ≤ n) {c : SV n → Fin (n + 1)} (hc : IsPanchromatic (sunflower n) c) :
    uniqueVerts c = univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
  ext v
  simp only [uniqueVerts, mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
  rcases v with j | i
  · simp only [Sum.inl.injEq, exists_eq, iff_true]
    intro w hw
    rcases w with j' | i'
    · have := injOn_petal hc ⟨0, by omega⟩ (mem_petal.2 (Or.inl rfl)) (mem_petal.2 (Or.inl rfl)) hw
      exact this
    · exact injOn_petal hc i' (mem_petal.2 (Or.inr rfl)) (mem_petal.2 (Or.inl rfl)) hw
  · simp only [reduceCtorEq, exists_false, iff_false, not_forall]
    -- another petal tip has the same colour
    obtain ⟨i', hi'⟩ : ∃ i' : Fin n, i' ≠ i := by
      by_cases h : (i : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
    have he : petal n i ∈ sunflower n := mem_image_of_mem _ (mem_univ _)
    obtain ⟨v, hv, hcv⟩ := hc _ he (c (Sum.inr i'))
    rcases mem_petal.1 hv with hl | rfl
    · rcases v with j | j
      · have := injOn_petal hc i' (mem_petal.2 (Or.inl rfl)) (mem_petal.2 (Or.inr rfl)) hcv
        simp at this
      · simp at hl
    · exact ⟨Sum.inr i', hcv.symm, by simpa using hi'⟩

/-- The bipanchromatic `n`-colouring `s_i, p_i ↦ i`. -/
def bipanColouring (n : ℕ) : SV n → Fin n
  | Sum.inl i => i
  | Sum.inr i => i

lemma bipanColouring_pan : IsPanchromatic (sunflower n) (bipanColouring n) := by
  intro e he j
  obtain ⟨i, -, rfl⟩ := mem_image.1 he
  exact ⟨Sum.inl j, mem_petal.2 (Or.inl rfl), rfl⟩

lemma bipanColouring_unique : uniqueVerts (bipanColouring n) = ∅ := by
  ext v
  simp only [uniqueVerts, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_forall]
  rcases v with i | i
  · exact ⟨Sum.inr i, rfl, by simp⟩
  · exact ⟨Sum.inl i, rfl, by simp⟩

/-- A colouring in which every colour is used (here: panchromatic with a hyperedge) and no colour
is unique uses each colour at least twice, so `2k ≤ |V|`. -/
lemma two_mul_le_of_bipan {k : ℕ} {c : V → Fin k} (hsurj : ∀ i, ∃ v, c v = i)
    (hu : uniqueVerts c = ∅) : 2 * k ≤ Fintype.card V := by
  have hfib : ∀ i : Fin k, 2 ≤ (univ.filter fun v => c v = i).card := by
    intro i
    obtain ⟨v, rfl⟩ := hsurj i
    have hv : v ∉ uniqueVerts c := by rw [hu]; exact notMem_empty v
    simp only [uniqueVerts, mem_filter, mem_univ, true_and, not_forall] at hv
    obtain ⟨w, hw, hwv⟩ := hv
    have : ({v, w} : Finset V) ⊆ univ.filter fun u => c u = c v := by
      intro u hu; simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl <;> simp [hw]
    have h2 : ({v, w} : Finset V).card = 2 := card_pair (Ne.symm hwv)
    exact h2 ▸ card_le_card this
  rw [← card_univ, card_eq_sum_card_fiberwise (f := c) (t := univ) (fun _ _ => mem_univ _)]
  calc 2 * k = ∑ _i : Fin k, 2 := by simp [mul_comm]
    _ ≤ _ := sum_le_sum fun i _ => hfib i

/-- **Sunflower theorem** (arXiv:2610.27133, Theorem 1): for `n ≥ 3`, `χ_P(S_n) = n + 1`,
`α(S_n) = n` and `χ_B(S_n) = n`. -/
theorem sunflower_parameters (hn : 3 ≤ n) :
    chiP (sunflower n) = n + 1 ∧ alpha (sunflower n) = n ∧ chiB (sunflower n) = n := by
  have hP : chiP (sunflower n) = n + 1 := by
    apply IsGreatest.csSup_eq
    exact ⟨⟨panColouring n, panColouring_pan⟩, fun k ⟨c, hc⟩ => le_of_pan (by omega) hc⟩
  refine ⟨hP, ?_, ?_⟩
  · rw [alpha, hP, alphaK]
    have : {m | ∃ c : SV n → Fin (n + 1), IsPanchromatic (sunflower n) c ∧
        (uniqueVerts c).card = m} = {n} := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨c, hc, rfl⟩
        rw [uniqueVerts_eq (by omega) hc]; simp
      · intro hm
        exact ⟨panColouring n, panColouring_pan, by rw [uniqueVerts_eq (by omega) panColouring_pan, hm]; simp⟩
    rw [this, csInf_singleton]
  · apply IsGreatest.csSup_eq
    refine ⟨⟨bipanColouring n, bipanColouring_pan, bipanColouring_unique⟩, ?_⟩
    rintro k ⟨c, hc, hu⟩
    have hsurj : ∀ i, ∃ v, c v = i := fun i => by
      obtain ⟨v, -, hv⟩ := hc _ (mem_image_of_mem _ (mem_univ ⟨0, by omega⟩)) i
      exact ⟨v, hv⟩
    have := two_mul_le_of_bipan hsurj hu
    rw [card_SV] at this
    omega

/-- The excess `χ_B - (χ_P - ⌈α/2⌉)` of `S_n` is `⌈n/2⌉ - 1`. -/
theorem sunflower_excess (hn : 3 ≤ n) :
    chiB (sunflower n) = chiP (sunflower n) - (alpha (sunflower n) + 1) / 2 + ((n + 1) / 2 - 1) := by
  obtain ⟨h1, h2, h3⟩ := sunflower_parameters hn
  rw [h1, h2, h3]
  omega

lemma sunflower_nonempty (hn : 1 ≤ n) : (sunflower n).Nonempty :=
  ⟨_, mem_image_of_mem (petal n) (mem_univ ⟨0, hn⟩)⟩

lemma sunflower_card_ge (e : Finset (SV n)) (he : e ∈ sunflower n) (hn : 1 ≤ n) : 2 ≤ e.card := by
  obtain ⟨i, -, rfl⟩ := mem_image.1 he
  rw [card_petal]; omega

/-- **The conjecture of Lalou et al. is false**: `S_3` (six vertices, three hyperedges) has
`χ_B = 3` but `χ_P - ⌈α/2⌉ = 4 - 2 = 2`. -/
theorem not_conjecture : ¬ Conjecture := by
  intro h
  have := h (SV 3) (sunflower 3) (by rw [card_SV]; norm_num) (sunflower_nonempty (by norm_num))
    (fun e he => sunflower_card_ge e he (by norm_num))
  obtain ⟨h1, h2, h3⟩ := sunflower_parameters (n := 3) le_rfl
  rw [h1, h2, h3] at this
  norm_num at this

/-- **No constant fixes it**: for every `C` there is a hypergraph (satisfying the conjecture's
hypotheses) with `χ_B > χ_P - ⌈α/2⌉ + C`. -/
theorem excess_unbounded (C : ℕ) :
    ∃ m, 2 ≤ Fintype.card (SV m) ∧ (sunflower m).Nonempty ∧ (∀ e ∈ sunflower m, 2 ≤ e.card) ∧
      chiP (sunflower m) - (alpha (sunflower m) + 1) / 2 + C < chiB (sunflower m) := by
  refine ⟨2 * C + 3, by rw [card_SV]; omega, sunflower_nonempty (by omega),
    fun e he => sunflower_card_ge e he (by omega), ?_⟩
  obtain ⟨h1, h2, h3⟩ := sunflower_parameters (n := 2 * C + 3) (by omega)
  rw [h1, h2, h3]
  omega

end OpenProblemsLab.Bipanchromatic
