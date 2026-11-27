import Lab.LocalAntimagic.Caterpillar

/-!
# The 43-vertex counterexample `T₃ = Cat(8, 7, 25)`

Brondani–França (arXiv:2610.22783, Theorem 4.1): the caterpillar `T₃` with spine `a – b – c`
carrying `8`, `7`, `25` leaves (degrees `9, 9, 26`, `m = 42` edges, `40` leaves, `43` vertices) has
`χ_la(T₃) = 43 = ℓ(T₃) + 3`. It has the fewest possible internal vertices (three) for a
counterexample to the leaf conjecture.

* Every local antimagic labelling has 43 distinct weights: leaf weights are distinct and at most
  `42`; spine weights are at least `45`; `wt a, wt b ≤ 342 < 351 ≤ wt c`; and `wt a ≠ wt b` because
  `a`, `b` are adjacent.
* A local antimagic labelling exists (the paper cites Haslegrave 2018; we argue directly): take any
  labelling; if `wt a = wt b`, swap the labels of a leaf edge at `a` and a leaf edge at `b`, which
  moves the two weights in opposite directions by the nonzero difference of the labels. All other
  adjacent pairs are separated by the degree bounds.
-/

namespace OpenProblemsLab.LocalAntimagic

open Finset SimpleGraph

/-! ### Swapping two labels -/

section Swap

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `f` followed by the transposition of the labels of `e₁` and `e₂`. -/
def swapLab (f : Labelling G) (e₁ e₂ : G.edgeSet) : Labelling G :=
  f.trans (Equiv.swap (f e₁) (f e₂))

omit [DecidableEq V] in
theorem lab_swapLab_of_ne (f : Labelling G) (e₁ e₂ : G.edgeSet) {e : Sym2 V}
    (h1 : e ≠ e₁.1) (h2 : e ≠ e₂.1) : lab (swapLab f e₁ e₂) e = lab f e := by
  unfold lab
  split_ifs with he
  · simp only [swapLab, Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact fun h => h1 (congrArg Subtype.val (f.injective h))
    · exact fun h => h2 (congrArg Subtype.val (f.injective h))
  · rfl

omit [DecidableEq V] in
theorem lab_swapLab_left (f : Labelling G) (e₁ e₂ : G.edgeSet) :
    lab (swapLab f e₁ e₂) e₁.1 = lab f e₂.1 := by
  simp [lab, swapLab, e₁.2, e₂.2]

/-- Swapping moves the weight of a vertex at `e₁` but not at `e₂` by `lab e₂ − lab e₁`. -/
theorem wt_swapLab (f : Labelling G) (e₁ e₂ : G.edgeSet) (v : V)
    (h1 : e₁.1 ∈ G.incidenceFinset v) (h2 : e₂.1 ∉ G.incidenceFinset v) :
    wt (swapLab f e₁ e₂) v + lab f e₁.1 = wt f v + lab f e₂.1 := by
  unfold wt
  rw [← add_sum_erase _ _ h1, ← add_sum_erase _ _ h1, lab_swapLab_left]
  have : ∑ e ∈ (G.incidenceFinset v).erase e₁.1, lab (swapLab f e₁ e₂) e =
      ∑ e ∈ (G.incidenceFinset v).erase e₁.1, lab f e := by
    refine sum_congr rfl fun e he => lab_swapLab_of_ne f e₁ e₂ (ne_of_mem_erase he) ?_
    rintro rfl; exact h2 (mem_of_mem_erase he)
  rw [this]; ring

end Swap

/-! ### `T₃` -/

/-- Spine degrees of `T₃`. -/
def d3 : Fin 3 → ℕ := ![9, 9, 26]

theorem d3_two_le : ∀ i, 2 ≤ d3 i := by decide

theorem card_edges_T3 : Fintype.card (Cat d3).edgeSet = 42 := by
  have := card_edges (d := d3) (by norm_num) d3_two_le
  have hs : ∑ i, d3 i = 44 := by decide
  omega

theorem numLeaves_T3 : numLeaves (Cat d3) = 40 := by
  rw [numLeaves_eq (by norm_num) d3_two_le]
  simp [pl, d3, Fin.sum_univ_three]

theorem card_T3 : Fintype.card (CV d3) = 43 := by
  rw [card_CV]; simp [pl, d3, Fin.sum_univ_three]

theorem deg_T3 (i : Fin 3) : (Cat d3).degree (.inl i) = d3 i :=
  degree_spine (by norm_num) d3_two_le i

/-- Weight bounds: every spine weight is above `42`, `wt a, wt b ≤ 342`, `wt c ≥ 351`. -/
theorem T3_bounds (f : Labelling (Cat d3)) :
    (∀ i, 42 < wt f (.inl i)) ∧ wt f (.inl 0) ≤ 342 ∧ wt f (.inl 1) ≤ 342 ∧ 351 ≤ wt f (.inl 2) := by
  have hm := card_edges_T3
  have hb := fun i => wt_bounds f (.inl i)
  simp only [deg_T3] at hb
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
  rw [show d3 0 = 9 from rfl] at h0
  rw [show d3 1 = 9 from rfl] at h1
  rw [show d3 2 = 26 from rfl] at h2
  refine ⟨fun i => ?_, by omega, by omega, by omega⟩
  have := hb i
  have : 9 ≤ d3 i := by fin_cases i <;> decide
  nlinarith

/-- A labelling of `T₃` is local antimagic iff `wt a ≠ wt b`; then all 43 weights are distinct. -/
theorem T3_injective (f : Labelling (Cat d3)) (hab : wt f (.inl 0) ≠ wt f (.inl 1)) :
    Function.Injective (wt f) := by
  obtain ⟨hs, ha, hb, hc⟩ := T3_bounds f
  have hm := card_edges_T3
  rintro (i | x) (j | y) h
  · congr 1
    have hval : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hval i with rfl | rfl | rfl <;> rcases hval j with rfl | rfl | rfl <;>
      first | rfl | omega
  · have := hs i; have := wt_leaf_le f _ (degree_leaf y); omega
  · have := hs j; have := wt_leaf_le f _ (degree_leaf x); omega
  · by_contra hxy
    exact wt_leaf_ne f (degree_leaf x) (degree_leaf y) hxy (not_adj_rr x y) h

theorem T3_localAntimagic_iff (f : Labelling (Cat d3)) :
    IsLocalAntimagic (Cat d3) f ↔ wt f (.inl 0) ≠ wt f (.inl 1) :=
  ⟨fun h => h _ _ (by simp), fun h u v huv hw => huv.ne (T3_injective f h hw)⟩

/-- A local antimagic labelling of `T₃` exists. -/
theorem T3_exists : ∃ f : Labelling (Cat d3), IsLocalAntimagic (Cat d3) f := by
  let f0 : Labelling (Cat d3) := Fintype.equivFin _
  by_cases h : wt f0 (.inl 0) = wt f0 (.inl 1)
  · let x : Σ i : Fin 3, Fin (pl d3 i) := ⟨0, ⟨0, by simp [pl, d3]⟩⟩
    let y : Σ i : Fin 3, Fin (pl d3 i) := ⟨1, ⟨0, by simp [pl, d3]⟩⟩
    let e₁ : (Cat d3).edgeSet := ⟨s(.inl 0, .inr x), by simp [x]⟩
    let e₂ : (Cat d3).edgeSet := ⟨s(.inl 1, .inr y), by simp [y]⟩
    have ha := wt_swapLab f0 e₁ e₂ (.inl 0) (by simp [e₁, x])
      (by simp [e₂, y, SimpleGraph.incidenceSet])
    have hb := wt_swapLab f0 e₂ e₁ (.inl 1) (by simp [e₂, y])
      (by simp [e₁, x, SimpleGraph.incidenceSet])
    have hswap : swapLab f0 e₂ e₁ = swapLab f0 e₁ e₂ := by
      unfold swapLab; rw [Equiv.swap_comm]
    rw [hswap] at hb
    have hne : lab f0 e₁.1 ≠ lab f0 e₂.1 := fun hl => by
      have := lab_injOn f0 e₁.2 e₂.2 hl
      rcases Sym2.eq_iff.1 this with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp at h1
    refine ⟨swapLab f0 e₁ e₂, (T3_localAntimagic_iff _).2 fun h' => hne ?_⟩
    omega
  · exact ⟨f0, (T3_localAntimagic_iff _).2 h⟩

/-- **Brondani–França, Theorem 4.1.** `T₃` is a tree on 43 vertices with 40 leaves and
`χ_la(T₃) = 43 = ℓ(T₃) + 3`. -/
theorem T3 : (Cat d3).IsTree ∧ Fintype.card (CV d3) = 43 ∧ numLeaves (Cat d3) = 40 ∧
    chiLA (Cat d3) = 43 := by
  refine ⟨cat_isTree (by norm_num) d3_two_le, card_T3, numLeaves_T3, ?_⟩
  obtain ⟨f, hf⟩ := T3_exists
  have hall : ∀ g : Labelling (Cat d3), IsLocalAntimagic (Cat d3) g →
      (univ.image (wt g)).card = 43 := fun g hg => by
    rw [card_image_of_injective _ (T3_injective g ((T3_localAntimagic_iff g).1 hg)), card_univ,
      card_T3]
  apply le_antisymm
  · exact Nat.sInf_le ⟨f, hf, hall f hf⟩
  · refine le_csInf ⟨_, f, hf, rfl⟩ ?_
    rintro n ⟨g, hg, rfl⟩
    rw [hall g hg]

/-- `T₃` alone refutes the leaf conjecture. -/
theorem not_leafConjecture_T3 : ¬ LeafConjecture := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := T3
  have := h _ (Cat d3) h1 (by omega)
  omega

end OpenProblemsLab.LocalAntimagic
