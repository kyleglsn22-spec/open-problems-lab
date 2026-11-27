import Lab.PartialList.Counterexample

/-!
# Connected counterexamples with a large gap (answering a question of Noel)

Noel (arXiv:2609.23291) disproved the Partial List Colouring Conjecture with a 14-vertex graph
`G` (`Lab/PartialList/Counterexample.lean`). He remarks that the additive gap in his example is
small (at most `9` vertices can be coloured, against the promised `28/3`), that disjoint copies
inflate it, and that "it may be interesting to try to cook up connected counterexamples which
achieve a large gap from the conjecture."

We give such a family. `Chain t` is a path of `t` copies of Noel's graph: vertex `3` (a
non-private vertex of the first triangle) of copy `j + 1` is joined to vertex `2` (the private
vertex of the first triangle) of copy `j`. Then, for every `t ≥ 1`:

* `chain_connected`: `Chain t` is connected;
* `listChromaticNumber_chain`: `χ_ℓ(Chain t) = 3`;
* `chain_partial_le`: from Noel's lists on every copy, at most `9 t` of the `n = 14 t` vertices
  can be properly coloured, while the conjecture promises `n · 2 / 3 = 28 t / 3`.

So the gap is at least `t / 3 = n / 42`, linear in the number of vertices (`connected_gap`).
Chappell's theorem (at least `(6/7) · n ℓ / k` vertices can always be coloured) caps the gap at
`2n/21` for `k = 3, ℓ = 2`, so a linear gap is the best possible order.

## Proof

* Upper bound: adding edges only removes proper colourings, and inside each copy Noel's bound
  gives at most 9 coloured vertices.
* 3-choosable: colour the copies in order. Copy `j + 1` sees one already coloured neighbour, at
  its vertex `3`. So it suffices that Noel's graph stays colourable from 3-lists when vertex `3`
  must avoid one given colour `f` (`colour_avoid`). This is Noel's argument with one change: the
  first triangle, whose vertex `3` now has the 2-list `X = L 3 \ {f}`, rules out at most 2 of the
  9 terminal pairs (`bad_sub`), the same as the other three triangles, so `4 · 2 = 8 < 9` still.
-/

namespace OpenProblemsLab.PartialList

open Finset SimpleGraph

/-! ### Noel's graph when vertex `3` must avoid one colour -/

section Avoid

/-- The first triangle can be finished after the terminals took `c, d`: there are colours
`x ∈ X`, `y ∈ Y` for its two non-private vertices, avoiding `c, d` and each other. -/
def Good (X Y : Finset ℕ) (c d : ℕ) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, x ≠ c ∧ x ≠ d ∧ y ≠ c ∧ y ≠ d ∧ x ≠ y

theorem good_of {X Y : Finset ℕ} {c d : ℕ} (hX : (X \ {c, d}).Nonempty)
    (hY : 2 ≤ (Y \ {c, d}).card) : Good X Y c d := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy, hy'⟩ := exists_mem_notMem (s := Y \ {c, d}) (t := {x})
    (by rw [card_singleton]; omega)
  simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hx hy hy'
  exact ⟨x, hx.1, y, hy.1, hx.2.1, hx.2.2, hy.2.1, hy.2.2, fun h => hy' h.symm⟩

/-- If the first triangle cannot be finished, then either `X ⊆ {c, d}`, or `c, d ∈ Y` and
`X ⊆ Y`. -/
theorem bad_cases {X Y : Finset ℕ} (hY : Y.card = 3) {c d : ℕ}
    (hbad : ¬ Good X Y c d) : X ⊆ {c, d} ∨ (c ∈ Y ∧ d ∈ Y ∧ X ⊆ Y) := by
  by_cases hXs : X ⊆ {c, d}
  · exact Or.inl hXs
  right
  obtain ⟨x0, hx0, hx0'⟩ := Finset.not_subset.1 hXs
  by_cases hcY : c ∈ Y ∧ d ∈ Y
  · refine ⟨hcY.1, hcY.2, ?_⟩
    intro x hx
    by_contra hxY
    have h1 : 1 ≤ (Y \ {c, d}).card := by
      have := Finset.le_card_sdiff ({c, d} : Finset ℕ) Y
      have := card_pair_le c d
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.1 (by omega : 0 < (Y \ {c, d}).card)
    have hxcd : x ∉ ({c, d} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun h => hxY (h ▸ hcY.1), fun h => hxY (h ▸ hcY.2)⟩
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hy hxcd
    exact hbad ⟨x, hx, y, hy.1, hxcd.1, hxcd.2, hy.2.1, hy.2.2, fun h => hxY (h ▸ hy.1)⟩
  · exact absurd (good_of ⟨x0, mem_sdiff.2 ⟨hx0, hx0'⟩⟩ (two_le_sdiff_two hY hcY)) hbad

/-- All pairs `(c, d)` (with `c ≠ d`) for which the first triangle cannot be finished lie inside
one set `Z` of at most 3 colours. -/
theorem bad_sub {X Y : Finset ℕ} (hX2 : 2 ≤ X.card) (hX3 : X.card ≤ 3) (hY : Y.card = 3) :
    ∃ Z : Finset ℕ, Z.card ≤ 3 ∧ ∀ c d, c ≠ d → ¬ Good X Y c d → c ∈ Z ∧ d ∈ Z := by
  -- `X ⊆ {c, d}` forces `X = {c, d}`
  have hpair : ∀ c d, X ⊆ {c, d} → c ∈ X ∧ d ∈ X := by
    intro c d h
    have he : X = {c, d} := Finset.eq_of_subset_of_card_le h (by have := card_pair_le c d; omega)
    rw [he]
    simp
  by_cases hXY : X ⊆ Y
  · refine ⟨Y, hY.le, fun c d _ hbad => ?_⟩
    rcases bad_cases hY hbad with h | h
    · exact ⟨hXY (hpair c d h).1, hXY (hpair c d h).2⟩
    · exact ⟨h.1, h.2.1⟩
  · refine ⟨X, hX3, fun c d _ hbad => ?_⟩
    rcases bad_cases hY hbad with h | h
    · exact hpair c d h
    · exact absurd h.2.2 hXY

/-- Two disjoint sets meet a set of at most 3 colours in at most `2` pairs. -/
theorem prod_inter_card_le {A B Z : Finset ℕ} (hAB : Disjoint A B) (hZ : Z.card ≤ 3) :
    ((A ∩ Z) ×ˢ (B ∩ Z)).card ≤ 2 := by
  rw [card_product]
  apply mul_le_two
  have hdisj : Disjoint (A ∩ Z) (B ∩ Z) :=
    Disjoint.mono inter_subset_left inter_subset_left hAB
  rw [← card_union_of_disjoint hdisj]
  calc ((A ∩ Z) ∪ (B ∩ Z)).card ≤ Z.card := card_le_card (union_subset inter_subset_right
        inter_subset_right)
    _ ≤ 3 := hZ

/-- **Choosing the terminal colours when vertex `3` must avoid `f`.** -/
theorem terminal_choice_avoid (L : Fin 14 → Finset ℕ) (hL : ∀ v, (L v).card = 3) (f : ℕ) :
    ∃ c ∈ L 0, ∃ d ∈ L 1, Good (L 3 \ {f}) (L 4) c d ∧
      ∀ v ∈ ({6, 9, 12} : Finset (Fin 14)), 2 ≤ (L v \ {c, d}).card := by
  have hX2 : 2 ≤ (L 3 \ {f}).card := by
    have := Finset.le_card_sdiff ({f} : Finset ℕ) (L 3)
    rw [card_singleton, hL 3] at this
    omega
  have hX3 : (L 3 \ {f}).card ≤ 3 := (card_le_card sdiff_subset).trans (hL 3).le
  by_cases hi : (L 0 ∩ L 1).Nonempty
  · obtain ⟨x, hx⟩ := hi
    rw [mem_inter] at hx
    refine ⟨x, hx.1, x, hx.2, good_of ?_ (two_le_sdiff_one (hL 4) x), fun v _ =>
      two_le_sdiff_one (hL v) x⟩
    apply Finset.card_pos.1
    have := Finset.le_card_sdiff ({x, x} : Finset ℕ) (L 3 \ {f})
    rw [pair_eq_singleton, card_singleton] at this
    rw [pair_eq_singleton]
    have h2 := hX2
    omega
  · rw [not_nonempty_iff_eq_empty] at hi
    have hAB : Disjoint (L 0) (L 1) := disjoint_iff_inter_eq_empty.2 hi
    obtain ⟨Z, hZ, hZbad⟩ := bad_sub hX2 hX3 (hL 4)
    set U : Finset (Fin 14) := {6, 9, 12} with hU
    set bad := U.biUnion (fun v => (L 0 ∩ L v) ×ˢ (L 1 ∩ L v)) ∪ (L 0 ∩ Z) ×ˢ (L 1 ∩ Z)
      with hbad
    have hcard : bad.card ≤ 8 := by
      calc bad.card ≤ (U.biUnion (fun v => (L 0 ∩ L v) ×ˢ (L 1 ∩ L v))).card
            + ((L 0 ∩ Z) ×ˢ (L 1 ∩ Z)).card := card_union_le _ _
        _ ≤ (∑ v ∈ U, ((L 0 ∩ L v) ×ˢ (L 1 ∩ L v)).card) + 2 :=
            add_le_add card_biUnion_le (prod_inter_card_le hAB hZ)
        _ ≤ (∑ _v ∈ U, 2) + 2 :=
            add_le_add (sum_le_sum fun v _ => prod_inter_card_le hAB (hL v).le) le_rfl
        _ = 8 := by simp [hU]
    have hall : (L 0 ×ˢ L 1).card = 9 := by rw [card_product, hL 0, hL 1]
    obtain ⟨⟨c, d⟩, hcd, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show bad.card < (L 0 ×ˢ L 1).card by omega)
    rw [mem_product] at hcd
    have hne : c ≠ d := by
      rintro rfl
      exact Finset.disjoint_left.1 hAB hcd.1 hcd.2
    refine ⟨c, hcd.1, d, hcd.2, ?_, fun v hv => two_le_sdiff_two (hL v) ?_⟩
    · by_contra hg
      obtain ⟨hcZ, hdZ⟩ := hZbad c d hne hg
      apply hnot
      rw [hbad]
      exact mem_union_right _ (mem_product.2 ⟨mem_inter.2 ⟨hcd.1, hcZ⟩, mem_inter.2 ⟨hcd.2, hdZ⟩⟩)
    · intro h
      apply hnot
      rw [hbad]
      refine mem_union_left _ (mem_biUnion.2 ⟨v, hv, ?_⟩)
      exact mem_product.2 ⟨mem_inter.2 ⟨hcd.1, h.1⟩, mem_inter.2 ⟨hcd.2, h.2⟩⟩

/-- **Noel's graph stays colourable from 3-lists when vertex `3` must avoid a colour `f`.** -/
theorem colour_avoid (L : Fin 14 → Finset ℕ) (hL : ∀ v, (L v).card = 3) (f : ℕ) :
    ∃ C : G.Coloring ℕ, (∀ v, C v ∈ L v) ∧ C 3 ≠ f := by
  obtain ⟨c, hc, d, hd, ⟨x0, hx0f, y0, hy0, c0, d0, a0, b0, e0⟩, hgood⟩ :=
    terminal_choice_avoid L hL f
  rw [mem_sdiff, mem_singleton] at hx0f
  obtain ⟨hx0, hf⟩ := hx0f
  obtain ⟨z0, hz0, hz0'⟩ := exists_mem_notMem (s := L 2) (t := {x0, y0})
    (by have := card_pair_le x0 y0; rw [hL 2]; omega)
  simp only [mem_insert, mem_singleton, not_or] at hz0'
  obtain ⟨f0, g0⟩ := hz0'
  obtain ⟨z1, hz1, x1, hx1, y1, hy1, a1, b1, c1, d1, e1, f1, g1⟩ :=
    tri_extend (hL 5) (hL 7) (hgood 6 (by decide))
  obtain ⟨z2, hz2, x2, hx2, y2, hy2, a2, b2, c2, d2, e2, f2, g2⟩ :=
    tri_extend (hL 8) (hL 10) (hgood 9 (by decide))
  obtain ⟨z3, hz3, x3, hx3, y3, hy3, a3, b3, c3, d3, e3, f3, g3⟩ :=
    tri_extend (hL 11) (hL 13) (hgood 12 (by decide))
  let col : Fin 14 → ℕ := ![c, d, z0, x0, y0, z1, x1, y1, z2, x2, y2, z3, x3, y3]
  refine ⟨Coloring.mk col ?_, ?_, ?_⟩
  · intro u v h
    fin_cases u <;> fin_cases v <;>
      first
      | exact absurd h (by decide)
      | (simp only [col, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
         first
         | assumption
         | exact fun e => absurd e.symm ‹_›)
  · intro v
    fin_cases v <;> simpa [col]
  · change col 3 ≠ f
    simpa [col] using hf

end Avoid

/-! ### The chain of `t` copies -/

section Chain

variable {t : ℕ}

/-- Adjacency in the chain: Noel's graph inside each copy, plus an edge from vertex `2` of copy
`j` to vertex `3` of copy `j + 1`. -/
def ChainAdj (t : ℕ) (a b : Fin t × Fin 14) : Prop :=
  (a.1 = b.1 ∧ G.Adj a.2 b.2) ∨ (a.1.val + 1 = b.1.val ∧ a.2 = 2 ∧ b.2 = 3) ∨
    (b.1.val + 1 = a.1.val ∧ b.2 = 2 ∧ a.2 = 3)

/-- **The chain**: `t` copies of Noel's graph, consecutive copies joined by one edge. It has
`14 t` vertices. -/
def Chain (t : ℕ) : SimpleGraph (Fin t × Fin 14) where
  Adj := ChainAdj t
  symm := by
    refine ⟨?_⟩
    intro a b h
    rcases h with ⟨h1, h2⟩ | h | h
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := by
    refine ⟨?_⟩
    intro a h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact G.irrefl h2
    · omega
    · omega

theorem chain_adj_in {j : Fin t} {u v : Fin 14} (h : G.Adj u v) : (Chain t).Adj (j, u) (j, v) :=
  Or.inl ⟨rfl, h⟩

/-! #### Upper bound: at most `9 t` vertices -/

/-- Noel's lists on every copy. -/
def Lchain (t : ℕ) (a : Fin t × Fin 14) : Finset ℕ := Ln a.2

theorem Lchain_card (a : Fin t × Fin 14) : (Lchain t a).card = 2 := Ln_card a.2

/-- **At most `9 t` vertices** of `Chain t` can be properly coloured from Noel's lists. -/
theorem chain_partial_le {S : Finset (Fin t × Fin 14)} {c : Fin t × Fin 14 → ℕ}
    (hL : ∀ v ∈ S, c v ∈ Lchain t v)
    (hP : ∀ u ∈ S, ∀ v ∈ S, (Chain t).Adj u v → c u ≠ c v) : S.card ≤ 9 * t := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  calc ∑ j : Fin t, (S.filter (fun a => a.1 = j)).card ≤ ∑ _j : Fin t, 9 := by
        apply sum_le_sum
        intro j _
        set Sj : Finset (Fin 14) := univ.filter (fun v => (j, v) ∈ S) with hSj
        have hmap : S.filter (fun a => a.1 = j) =
            Sj.map ⟨fun v => (j, v), fun u v h => (Prod.mk.inj h).2⟩ := by
          ext ⟨i, v⟩
          simp only [mem_filter, mem_map, hSj, mem_univ, true_and]
          constructor
          · rintro ⟨h, rfl⟩
            exact ⟨v, h, rfl⟩
          · rintro ⟨w, hw, he⟩
            cases he
            exact ⟨hw, rfl⟩
        rw [hmap, card_map]
        refine partial_le_nine (S := Sj) (c := fun v => c (j, v)) ?_ ?_
        · intro v hv
          rw [hSj, mem_filter] at hv
          exact hL _ hv.2
        · intro u hu v hv h
          rw [hSj, mem_filter] at hu hv
          exact hP _ hu.2 _ hv.2 (chain_adj_in h)
    _ = 9 * t := by simp [mul_comm]

/-! #### `Chain t` is 3-choosable -/

/-- Colour the copies in order; copy `j + 1` makes its vertex `3` avoid the colour of vertex `2`
of copy `j`. -/
noncomputable def chainCol (M : ℕ → Fin 14 → Finset ℕ) (hM : ∀ j v, (M j v).card = 3) :
    ℕ → G.Coloring ℕ
  | 0 => Classical.choose (colour_avoid (M 0) (hM 0) 0)
  | j + 1 => Classical.choose (colour_avoid (M (j + 1)) (hM (j + 1)) (chainCol M hM j 2))

theorem chainCol_mem (M : ℕ → Fin 14 → Finset ℕ) (hM : ∀ j v, (M j v).card = 3) (j : ℕ)
    (v : Fin 14) : chainCol M hM j v ∈ M j v := by
  cases j with
  | zero => exact (Classical.choose_spec (colour_avoid (M 0) (hM 0) 0)).1 v
  | succ j =>
      exact (Classical.choose_spec
        (colour_avoid (M (j + 1)) (hM (j + 1)) (chainCol M hM j 2))).1 v

theorem chainCol_link (M : ℕ → Fin 14 → Finset ℕ) (hM : ∀ j v, (M j v).card = 3) (j : ℕ) :
    chainCol M hM (j + 1) 3 ≠ chainCol M hM j 2 :=
  (Classical.choose_spec (colour_avoid (M (j + 1)) (hM (j + 1)) (chainCol M hM j 2))).2

theorem chain_isKChoosable_three : (Chain t).IsKChoosable 3 := by
  intro L hL
  let M : ℕ → Fin 14 → Finset ℕ := fun j v => if h : j < t then L (⟨j, h⟩, v) else {0, 1, 2}
  have hM : ∀ j v, (M j v).card = 3 := by
    intro j v
    simp only [M]
    split_ifs
    · exact hL _
    · decide
  refine ⟨Coloring.mk (fun a => chainCol M hM a.1.val a.2) ?_, ?_⟩
  · intro a b h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · show chainCol M hM a.1.val a.2 ≠ chainCol M hM b.1.val b.2
      rw [h1]
      exact (chainCol M hM b.1.val).valid h2
    · show chainCol M hM a.1.val a.2 ≠ chainCol M hM b.1.val b.2
      rw [h2, h3, ← h1]
      exact (chainCol_link M hM _).symm
    · show chainCol M hM a.1.val a.2 ≠ chainCol M hM b.1.val b.2
      rw [h2, h3, ← h1]
      exact chainCol_link M hM _
  · intro a
    have := chainCol_mem M hM a.1.val a.2
    simp only [M, a.1.isLt, dite_true] at this
    exact this

/-! #### The list chromatic number is 3 -/

theorem chain_not_isKChoosable_of_le_two (ht : 1 ≤ t) {k : ℕ} (hk : k ≤ 2) :
    ¬ (Chain t).IsKChoosable k := by
  intro h
  obtain ⟨C⟩ := (IsKChoosable.colorable h).mono hk
  let j : Fin t := ⟨0, ht⟩
  have h23 := C.valid (chain_adj_in (j := j) (show G.Adj 2 3 by decide))
  have h24 := C.valid (chain_adj_in (j := j) (show G.Adj 2 4 by decide))
  have h34 := C.valid (chain_adj_in (j := j) (show G.Adj 3 4 by decide))
  generalize C (j, 2) = p, C (j, 3) = q, C (j, 4) = r at h23 h24 h34
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp_all

theorem listChromaticNumber_chain (ht : 1 ≤ t) : (Chain t).listChromaticNumber = 3 := by
  apply le_antisymm (Nat.sInf_le chain_isKChoosable_three)
  apply le_csInf ⟨3, chain_isKChoosable_three⟩
  intro k hk
  by_contra h
  exact chain_not_isKChoosable_of_le_two ht (by omega) hk

/-! #### `Chain t` is connected -/

/-- Inside Noel's graph every vertex is within two steps of terminal `0`. -/
theorem G_near_zero : ∀ v : Fin 14, ∃ w : Fin 14, (v = w ∨ G.Adj v w) ∧ (w = 0 ∨ G.Adj w 0) := by
  decide

theorem chain_reach_zero (j : Fin t) (v : Fin 14) : (Chain t).Reachable (j, v) (j, 0) := by
  obtain ⟨w, h1, h2⟩ := G_near_zero v
  have r1 : (Chain t).Reachable (j, v) (j, w) := by
    rcases h1 with rfl | h
    · rfl
    · exact (chain_adj_in h).reachable
  have r2 : (Chain t).Reachable (j, w) (j, 0) := by
    rcases h2 with rfl | h
    · rfl
    · exact (chain_adj_in h).reachable
  exact r1.trans r2

theorem chain_connected (ht : 1 ≤ t) : (Chain t).Connected := by
  let o : Fin t × Fin 14 := (⟨0, ht⟩, 0)
  have key : ∀ n (hn : n < t), (Chain t).Reachable (⟨n, hn⟩, 0) o := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
        intro hn
        have hn' : n < t := by omega
        have link : (Chain t).Adj ((⟨n + 1, hn⟩ : Fin t), 3) ((⟨n, hn'⟩ : Fin t), 2) :=
          Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
        exact ((chain_reach_zero _ 3).symm.trans link.reachable).trans
          ((chain_reach_zero _ 2).trans (ih hn'))
  have hall : ∀ a, (Chain t).Reachable a o := fun a =>
    (chain_reach_zero a.1 a.2).trans (key a.1.val a.1.isLt)
  have : Nonempty (Fin t × Fin 14) := ⟨o⟩
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

/-! ### The result -/

/-- **Connected counterexamples with a linear gap.** For every `t ≥ 1` there is a connected
graph on `n = 14 t` vertices with list chromatic number `3` and a 2-list assignment from which
every proper partial colouring colours at most `9 t` vertices. The conjecture promises
`n · 2 / 3 = 28 t / 3`, so the gap is at least `t / 3 = n / 42`: here
`n · 2 ≥ 3 · |S| + t`. -/
theorem connected_gap (t : ℕ) (ht : 1 ≤ t) :
    ∃ H : SimpleGraph (Fin t × Fin 14), H.Connected ∧ H.listChromaticNumber = 3 ∧
      ∃ L : Fin t × Fin 14 → Finset ℕ, (∀ v, (L v).card = 2) ∧
        ∀ S : Finset (Fin t × Fin 14), ∀ c : Fin t × Fin 14 → ℕ, (∀ v ∈ S, c v ∈ L v) →
          (∀ u ∈ S, ∀ v ∈ S, H.Adj u v → c u ≠ c v) →
            S.card ≤ 9 * t ∧
            Fintype.card (Fin t × Fin 14) * 2 ≥ S.card * H.listChromaticNumber + t := by
  refine ⟨Chain t, chain_connected ht, listChromaticNumber_chain ht, Lchain t, Lchain_card,
    fun S c hL hP => ?_⟩
  have h9 := chain_partial_le hL hP
  refine ⟨h9, ?_⟩
  rw [listChromaticNumber_chain ht, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  omega

end Chain

end OpenProblemsLab.PartialList
