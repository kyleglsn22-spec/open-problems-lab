import Lab.ClawFree.Shapes

/-!
# The claw-free Schur-positivity conjecture is false

Prajapati (arXiv:2607.26364, Theorem 1; independently Matherne–Morales arXiv:2607.21508): let `H`
be a 4-cycle `a b c d` with a triangle `a u v` at `a`, a triangle `c x y` at `c` and pendant edges
`b ℓ`, `d m`. Its line graph `G = L(H)` (12 vertices, 22 edges) is claw-free, and the coefficient
of `s_{(3,3,3,3)}` in `X_G` is `-64`.

We prove `not_clawFreeSchurPositivity`: `X_G` in four variables is not a non-negative combination
of Schur polynomials. The proof follows the paper's triangular inversion:

1. Monomial coefficients of `X_G` (`[x^α] X_G` = number of proper 4-colourings with colour-class
   sizes `α`), counted by the kernel via the verified backtracking list of `Enum`:
   `[x^{4422}] = 128`, `[x^{4332}] = 320`, `[x^{3333}] = 768`, and for every non-increasing `α`
   other than these three the coefficient is `0` (`chrom_support`).
2. Kostka numbers `K_{μ,α} = [x^α] s_μ` for `μ, α ∈ {4422, 4332, 3333}`, counted the same way.
3. Suppose `X_G = ∑ c_μ s_μ` with `c_μ ≥ 0`. Diagrams with five rows have `s_μ = 0` in four
   variables. For any other `μ` with `c_μ > 0`, the coefficient of `x^{rows of μ}` in `X_G` is at
   least `c_μ > 0`, so `μ` is one of the three shapes above. Comparing the coefficients of
   `x^{4422}`, `x^{4332}`, `x^{3333}` then gives `c_{3333} = 768 - 2·128 - 3·192 = -64`.

Vertices of `G` are the edges of `H`, numbered `0 … 11` as
`ab, bc, cd, da, au, av, uv, cx, cy, xy, bℓ, dm`, with `H`'s vertices
`a b c d u v x y ℓ m = 0 … 9`.
-/


namespace OpenProblemsLab.ClawFree.Counterexample

open MvPolynomial Finset OpenProblemsLab.ClawFree

/-! ### Which shapes can carry a positive coefficient -/

/-- If `μ` has at most four rows and `x^{rows of μ}` appears in `X_G`, then `μ` is one of the
three shapes `4422`, `4332`, `3333`. -/
theorem gen_antiOK : (Enum.gen colR 12).all antiOK = true := by
  have h := congrArg (·.2.2.2) summ_gen
  simp only [summ] at h
  exact h

theorem chrom_support (μ : YoungDiagram) (h4 : (4, 0) ∉ μ)
    (h : coeff (rowVec μ) (chromSym G 4) ≠ 0) : μ = D1 ∨ μ = D2 ∨ μ = D3 := by
  rw [chromSym, coeff_sum_prod_X] at h
  obtain ⟨κ, hκ⟩ := Finset.card_ne_zero.mp (by exact_mod_cast h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hκ
  have hmem : List.ofFn κ ∈ Enum.gen colR 12 :=
    (Enum.mem_gen _ _ _).mpr ⟨by simp, (Enum.valid_ofFn_iff _ _).mpr ((proper_iff κ).mp hκ.1)⟩
  have hok := List.all_eq_true.mp gen_antiOK _ hmem
  have hc : ∀ i : Fin 4, (List.ofFn κ).count i = μ.rowLen i := fun i => by
    rw [Enum.count_ofFn, ← content_apply, hκ.2, rowVec_apply]
  have c0 : (List.ofFn κ).count 0 = μ.rowLen 0 := hc 0
  have c1 : (List.ofFn κ).count 1 = μ.rowLen 1 := hc 1
  have c2 : (List.ofFn κ).count 2 = μ.rowLen 2 := hc 2
  have c3 : (List.ofFn κ).count 3 = μ.rowLen 3 := hc 3
  have a1 := μ.rowLen_anti 0 1 (by omega)
  have a2 := μ.rowLen_anti 1 2 (by omega)
  have a3 := μ.rowLen_anti 2 3 (by omega)
  simp only [antiOK, c0, c1, c2, c3, a1, a2, a3, decide_true, Bool.and_self, Bool.not_true,
    Bool.false_or, Bool.or_eq_true, beq_iff_eq, List.cons.injEq, and_true] at hok
  rcases hok with (h | h) | h
  · left
    exact eq_ofRowLens μ h4 _ _ rfl fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · right; left
    exact eq_ofRowLens μ h4 _ _ rfl fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · right; right
    exact eq_ofRowLens μ h4 _ _ rfl fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem D1_ne_D2 : D1 ≠ D2 := by
  intro h
  have : ((1, 3) : ℕ × ℕ) ∈ D1 := mem_ofRowLens_iff.mpr (by decide)
  rw [h] at this
  exact absurd (mem_ofRowLens_iff.mp this) (by decide)

theorem D1_ne_D3 : D1 ≠ D3 := by
  intro h
  have : ((0, 3) : ℕ × ℕ) ∈ D1 := mem_ofRowLens_iff.mpr (by decide)
  rw [h] at this
  exact absurd (mem_ofRowLens_iff.mp this) (by decide)

theorem D2_ne_D3 : D2 ≠ D3 := by
  intro h
  have : ((0, 3) : ℕ × ℕ) ∈ D2 := mem_ofRowLens_iff.mpr (by decide)
  rw [h] at this
  exact absurd (mem_ofRowLens_iff.mp this) (by decide)

/-! ### Main theorem -/

/-- `X_G` (in four variables) is not Schur-positive. -/
theorem not_schurPositive : ¬ SchurPositive (chromSym G 4) := by
  classical
  rintro ⟨s, c, h⟩
  have hco : ∀ α, coeff α (chromSym G 4) = ∑ μ ∈ s, (c μ : ℤ) * coeff α (schurPoly 4 μ) := by
    intro α
    rw [h, coeff_sum]
    exact Finset.sum_congr rfl fun μ _ => by rw [coeff_smul, smul_eq_mul]
  have hnn : ∀ α μ, 0 ≤ (c μ : ℤ) * coeff α (schurPoly 4 μ) := fun α μ =>
    mul_nonneg (by positivity) (coeff_schurPoly_nonneg _ _)
  have key : ∀ μ ∈ s, c μ ≠ 0 → (4, 0) ∉ μ → μ = D1 ∨ μ = D2 ∨ μ = D3 := by
    intro μ hμ hc h4
    apply chrom_support μ h4
    rw [hco]
    apply ne_of_gt
    calc (0 : ℤ) < (c μ : ℤ) * coeff (rowVec μ) (schurPoly 4 μ) :=
          mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hc)
            (lt_of_lt_of_le one_pos (one_le_coeff_rowVec μ h4))
      _ ≤ _ := Finset.single_le_sum
          (f := fun ν => (c ν : ℤ) * coeff (rowVec μ) (schurPoly 4 ν)) (fun ν _ => hnn _ ν) hμ
  have hred : ∀ α, coeff α (chromSym G 4) =
      ∑ μ ∈ ({D1, D2, D3} : Finset YoungDiagram),
        (if μ ∈ s then (c μ : ℤ) else 0) * coeff α (schurPoly 4 μ) := by
    intro α
    rw [hco]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem]
    refine (Finset.sum_subset Finset.inter_subset_right fun μ hμs hμT => ?_).symm
    have hnT : μ ∉ ({D1, D2, D3} : Finset YoungDiagram) :=
      fun hT => hμT (Finset.mem_inter.mpr ⟨hT, hμs⟩)
    by_cases hc : c μ = 0
    · simp [hc]
    by_cases h4 : (4, 0) ∈ μ
    · simp [schurPoly_eq_zero μ h4]
    exfalso
    apply hnT
    rcases key μ hμs hc h4 with rfl | rfl | rfl <;> simp
  have n1 : D1 ∉ ({D2, D3} : Finset YoungDiagram) := by simp [D1_ne_D2, D1_ne_D3]
  have n2 : D2 ∉ ({D3} : Finset YoungDiagram) := by simp [D2_ne_D3]
  have E1 := hred e4422
  have E2 := hred e4332
  have E3 := hred e3333
  rw [Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_singleton] at E1 E2 E3
  rw [K11, K21, K31, chrom_4422] at E1
  rw [K12, K22, K32, chrom_4332] at E2
  rw [K13, K23, K33, chrom_3333] at E3
  have h3 : (0 : ℤ) ≤ if D3 ∈ s then (c D3 : ℤ) else 0 := by split_ifs <;> positivity
  linarith

/-- **The claw-free Schur-positivity conjecture is false.** -/
theorem not_clawFreeSchurPositivity : ¬ ClawFreeSchurPositivity :=
  fun h => not_schurPositive (h (Fin 12) G G_isClawFree 4)

end OpenProblemsLab.ClawFree.Counterexample
