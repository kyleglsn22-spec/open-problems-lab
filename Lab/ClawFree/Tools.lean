import Lab.ClawFree.Defs
import Lab.ClawFree.Enum

/-!
# General facts about `chromSym` and `schurPoly`

* `coeff_sum_prod_X`: the coefficient of `x^α` in a sum of monomials `∏ d, x_{f d}` counts the
  `f` with content `α` (content = how many times each variable is used).
* `card_content_eq`: such counts for functions `Fin m → Fin k` under pairwise constraints are
  computed by the backtracking list of `Enum`.
* `schurPoly_eq_zero`: `s_μ(x_0, …, x_3) = 0` if `μ` has a fifth row.
* `one_le_coeff_rowVec`: otherwise `x^{rows of μ}` appears in `s_μ(x_0, …, x_3)` (the filling with
  `i` in row `i`).
-/

namespace OpenProblemsLab.ClawFree

open MvPolynomial Finset

/-- The content of `f : D → σ`: `α σ = #{d | f d = σ}`, as a finitely supported function. -/
noncomputable def content {D σ : Type*} [Fintype D] (f : D → σ) : σ →₀ ℕ :=
  ∑ d, Finsupp.single (f d) 1

theorem content_apply {D σ : Type*} [Fintype D] [DecidableEq σ] (f : D → σ) (i : σ) :
    content f i = (univ.filter fun d => f d = i).card := by
  rw [content, Finsupp.finsetSum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finsupp.single_apply]

theorem prod_X_eq_monomial {D σ : Type*} [Fintype D] (f : D → σ) :
    (∏ d, (X (f d) : MvPolynomial σ ℤ)) = monomial (content f) 1 := by
  simp [content, MvPolynomial.monomial_sum_one, X]

theorem coeff_sum_prod_X {D σ : Type*} [Fintype D] (S : Finset (D → σ)) (α : σ →₀ ℕ)
    [DecidablePred fun f : D → σ => content f = α] :
    coeff α (∑ f ∈ S, ∏ d, (X (f d) : MvPolynomial σ ℤ)) =
      ((S.filter fun f => content f = α).card : ℤ) := by
  classical
  simp only [prod_X_eq_monomial, coeff_sum]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs <;> simp_all [eq_comm]

/-- Counting functions `Fin m → Fin k` that satisfy pairwise constraints and have content `w`
via the backtracking list. -/
theorem card_content_eq {k m : ℕ} (R : ℕ → ℕ → Fin k → Fin k → Bool)
    (P : (Fin m → Fin k) → Prop) [DecidablePred P] (α : Fin k →₀ ℕ) (w : Fin k → ℕ)
    (hw : ∀ i, α i = w i)
    [DecidablePred fun f : Fin m → Fin k => P f ∧ content f = α]
    (hP : ∀ f, P f ↔ ∀ a b : Fin m, a < b → R a b (f a) (f b) = true) :
    (univ.filter fun f : Fin m → Fin k => P f ∧ content f = α).card =
      ((Enum.gen R m).filter fun l => (List.finRange k).all fun i => l.count i == w i).length := by
  classical
  rw [← Enum.card_filter_eq R P (fun f => content f = α) _ hP]
  · congr 1; ext f; simp
  · intro f
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq, Enum.count_ofFn]
    constructor
    · intro h i; rw [← hw i, ← h, content_apply]
    · intro h; ext i; rw [content_apply, h, hw]

/-! ### Schur polynomials in four variables -/

open scoped Classical in
theorem coeff_schurPoly {n : ℕ} (μ : YoungDiagram) (α : Fin n →₀ ℕ) :
    coeff α (schurPoly n μ) =
      ((univ.filter fun T : μ.cells → Fin n => IsSSYT μ T ∧ content T = α).card : ℤ) := by
  classical
  rw [schurPoly, coeff_sum_prod_X, Finset.filter_filter]

theorem coeff_schurPoly_nonneg {n : ℕ} (μ : YoungDiagram) (α : Fin n →₀ ℕ) :
    0 ≤ coeff α (schurPoly n μ) := by
  rw [coeff_schurPoly]; positivity

/-- A diagram with a fifth row has no semistandard filling from four letters. -/
theorem schurPoly_eq_zero (μ : YoungDiagram) (h : (4, 0) ∈ μ) : schurPoly 4 μ = 0 := by
  classical
  rw [schurPoly]
  refine Finset.sum_eq_zero fun T hT => ?_
  exfalso
  have hT : IsSSYT μ T := (Finset.mem_filter.mp hT).2
  have m : ∀ i ≤ 4, (i, 0) ∈ μ.cells := fun i hi =>
    (YoungDiagram.mem_cells _).mpr (μ.up_left_mem hi le_rfl h)
  have h01 := hT.2 ⟨_, m 0 (by omega)⟩ ⟨_, m 1 (by omega)⟩ rfl (by simp)
  have h12 := hT.2 ⟨_, m 1 (by omega)⟩ ⟨_, m 2 (by omega)⟩ rfl (by simp)
  have h23 := hT.2 ⟨_, m 2 (by omega)⟩ ⟨_, m 3 (by omega)⟩ rfl (by simp)
  have h34 := hT.2 ⟨_, m 3 (by omega)⟩ ⟨_, m 4 le_rfl⟩ rfl (by simp)
  have := (T ⟨_, m 4 le_rfl⟩).isLt
  simp only [Fin.lt_def] at h01 h12 h23 h34
  omega

/-- The row lengths of `μ` (first four rows) as an exponent vector. -/
noncomputable def rowVec (μ : YoungDiagram) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => μ.rowLen i

theorem rowVec_apply (μ : YoungDiagram) (i : Fin 4) : rowVec μ i = μ.rowLen i := rfl

/-- If `μ` has at most four rows, `x^{rows of μ}` appears in `s_μ(x_0, …, x_3)`: put `i` in every
cell of row `i`. -/
theorem one_le_coeff_rowVec (μ : YoungDiagram) (h : (4, 0) ∉ μ) :
    1 ≤ coeff (rowVec μ) (schurPoly 4 μ) := by
  classical
  have lt : ∀ c : μ.cells, c.1.1 < 4 := by
    intro c
    by_contra hc
    exact h (μ.up_left_mem (not_lt.mp hc) (Nat.zero_le c.1.2)
      ((YoungDiagram.mem_cells _).mp c.2))
  let T0 : μ.cells → Fin 4 := fun c => ⟨c.1.1, lt c⟩
  have hT0 : IsSSYT μ T0 :=
    ⟨fun a b hab _ => by simp [T0, hab],
     fun a b _ hab => by simp [T0, Fin.lt_def, hab]⟩
  have hc : content T0 = rowVec μ := by
    ext i
    rw [content_apply, rowVec_apply, YoungDiagram.rowLen_eq_card, YoungDiagram.row,
      ← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext ⟨x, y⟩
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype, Subtype.exists, exists_and_right, exists_eq_right, T0,
      Fin.ext_iff]
    constructor
    · rintro ⟨hm, rfl⟩; exact ⟨hm, rfl⟩
    · rintro ⟨hm, rfl⟩; exact ⟨hm, rfl⟩
  rw [coeff_schurPoly]
  exact_mod_cast Finset.card_pos.mpr ⟨T0, by simp [hT0, hc]⟩

/-- A diagram with at most four rows is determined by its row lengths. -/
theorem eq_ofRowLens (μ : YoungDiagram) (h : (4, 0) ∉ μ) (w : List ℕ) (hw : w.SortedGE)
    (hlen : w.length = 4) (hrow : ∀ i : Fin 4, μ.rowLen i = w[i]'(by omega)) :
    μ = YoungDiagram.ofRowLens w hw := by
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens]
  by_cases hi : i < 4
  · rw [YoungDiagram.mem_iff_lt_rowLen, hrow ⟨i, hi⟩]
    simp [hlen, hi]
  · constructor
    · intro hm
      exact absurd (μ.up_left_mem (by omega) (Nat.zero_le j) hm) h
    · rintro ⟨hl, -⟩; omega

/-! ### From fillings of a diagram to functions on `Fin m` -/

/-- Constraint between two cells at positions `p` (earlier) and `q` (later), for fillings listed
in row-major order. -/
def ssytRule (p q : ℕ × ℕ) {k : ℕ} (x y : Fin k) : Bool :=
  (!(p.1 == q.1) || decide (x ≤ y)) && (!(p.2 == q.2) || decide (x < y))

theorem ssyt_iff {m k : ℕ} (μ : YoungDiagram) (posN : ℕ → ℕ × ℕ) (e : Fin m ≃ μ.cells)
    (he : ∀ i, (e i).1 = posN i)
    (F1 : ∀ a b : Fin m, a < b → (posN a).1 = (posN b).1 → (posN a).2 ≤ (posN b).2)
    (F2 : ∀ a b : Fin m, a < b → (posN a).2 = (posN b).2 → (posN a).1 < (posN b).1)
    (T : μ.cells → Fin k) :
    IsSSYT μ T ↔ ∀ a b : Fin m, a < b →
      (fun a b x y => ssytRule (posN a) (posN b) x y) a b (T (e a)) (T (e b)) = true := by
  have cell_eq : ∀ a b : Fin m, posN a = posN b → a = b := by
    intro a b h
    apply e.injective
    apply Subtype.ext
    rw [he, he, h]
  constructor
  · rintro ⟨h1, h2⟩ a b hab
    simp only [ssytRule, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
      decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · by_cases hr : (posN a).1 = (posN b).1
      · exact Or.inr (h1 _ _ (by rw [he, he, hr]) (by rw [he, he]; exact F1 a b hab hr))
      · exact Or.inl hr
    · by_cases hc : (posN a).2 = (posN b).2
      · exact Or.inr (h2 _ _ (by rw [he, he, hc]) (by rw [he, he]; exact F2 a b hab hc))
      · exact Or.inl hc
  · intro h
    have h' : ∀ a b : Fin m, a < b →
        ((posN a).1 = (posN b).1 → T (e a) ≤ T (e b)) ∧
        ((posN a).2 = (posN b).2 → T (e a) < T (e b)) := by
      intro a b hab
      have := h a b hab
      simp only [ssytRule, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne, decide_eq_true_eq] at this
      exact ⟨fun hr => this.1.resolve_left (not_not.mpr hr),
        fun hc => this.2.resolve_left (not_not.mpr hc)⟩
    refine ⟨fun p q hr hc => ?_, fun p q hc hr => ?_⟩
    · obtain ⟨a, rfl⟩ := e.surjective p
      obtain ⟨b, rfl⟩ := e.surjective q
      rw [he, he] at hr hc
      rcases lt_trichotomy a b with hab | rfl | hab
      · exact (h' a b hab).1 hr
      · exact le_rfl
      · have := F1 b a hab hr.symm
        have hab' := cell_eq a b (Prod.ext hr (le_antisymm hc this))
        exact absurd hab' (ne_of_gt hab)
    · obtain ⟨a, rfl⟩ := e.surjective p
      obtain ⟨b, rfl⟩ := e.surjective q
      rw [he, he] at hr hc
      rcases lt_trichotomy a b with hab | rfl | hab
      · exact (h' a b hab).2 hc
      · exact absurd hr (lt_irrefl _)
      · exact absurd (F2 b a hab hc.symm) (not_lt.mpr hr.le)

/-- Kostka numbers `K_{μ,α} = [x^α] s_μ` from the backtracking list. -/
theorem coeff_schurPoly_eq_gen {m : ℕ} (μ : YoungDiagram) (posN : ℕ → ℕ × ℕ) (e : Fin m ≃ μ.cells)
    (he : ∀ i, (e i).1 = posN i)
    (F1 : ∀ a b : Fin m, a < b → (posN a).1 = (posN b).1 → (posN a).2 ≤ (posN b).2)
    (F2 : ∀ a b : Fin m, a < b → (posN a).2 = (posN b).2 → (posN a).1 < (posN b).1)
    (α : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) (hw : ∀ i, α i = w i) :
    coeff α (schurPoly 4 μ) =
      (((Enum.gen (fun a b x y => ssytRule (posN a) (posN b) x y) m).filter
        fun l => (List.finRange 4).all fun i => l.count i == w i).length : ℤ) := by
  classical
  rw [coeff_schurPoly, ← card_content_eq _ (fun f : Fin m → Fin 4 =>
    ∀ a b : Fin m, a < b → ssytRule (posN a) (posN b) (f a) (f b) = true) α w hw (fun f => Iff.rfl)]
  congr 1
  refine Finset.card_bij (fun T _ => T ∘ e) ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    refine ⟨(ssyt_iff μ posN e he F1 F2 T).mp hT.1, ?_⟩
    rw [← hT.2]
    simp only [content, Function.comp]
    exact Equiv.sum_comp e (fun c => Finsupp.single (T c) 1)
  · intro T₁ _ T₂ _ h
    funext c
    obtain ⟨a, rfl⟩ := e.surjective c
    exact congrFun h a
  · intro f hf
    refine ⟨f ∘ e.symm, ?_, by funext a; simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    have hfe : (f ∘ e.symm) ∘ e = f := by funext a; simp
    refine ⟨(ssyt_iff μ posN e he F1 F2 _).mpr (by simpa using hf.1), ?_⟩
    rw [← hf.2]
    simp only [content]
    rw [← Equiv.sum_comp e]
    simp

end OpenProblemsLab.ClawFree
