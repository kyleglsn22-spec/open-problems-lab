import Lab.ClawFree2.Shapes

/-!
# The second minimal counterexample to claw-free Schur-positivity

Prajapati (arXiv:2607.26364, Proposition 4) found, by an exhaustive computer census, exactly two
claw-free graphs on 12 vertices whose chromatic symmetric function is not Schur-positive. The first
(`[s_{3333}] X = −64`) is formalized in `Lab/ClawFree/`. This file formalizes the second: the graph
with graph6 code ``K?`CR@`bAbRB`` (12 vertices, 21 edges; a line graph), for which
`[s_{3333}] X_G = −40`. Wang–Zhang–Zhao (arXiv:2607.27166) call it `G₂` and show it is also the
smallest counterexample when graphs are ordered by edges first, then vertices.

Same method as `Lab/ClawFree/Counterexample.lean`:

1. Monomial coefficients (proper 4-colourings by class sizes), counted by the kernel:
   `[x^{5322}] = 24`, `[x^{4422}] = 176`, `[x^{4332}] = 440`, `[x^{3333}] = 1056`, and every other
   non-increasing class-size vector has coefficient `0` (`chrom_support`).
2. The 16 Kostka numbers between these four shapes.
3. If `X_G = ∑ c_μ s_μ` with `c_μ ≥ 0`, only the four shapes can carry positive coefficients, and
   triangular inversion forces `c_{5322} = 24`, `c_{4422} = 152`, `c_{4332} = 240` and
   `c_{3333} = 1056 − 3·24 − 2·152 − 3·240 = −40 < 0`, a contradiction.
-/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree
open OpenProblemsLab.ClawFree.Counterexample (mem_ofRowLens_iff)

/-! ### Which shapes can carry a positive coefficient -/

/-- Every proper colouring with non-increasing class sizes has one of the four contents. -/
theorem gen_antiOK : (Enum.gen colR 12).all antiOK = true := by
  have h := congrArg (·.2.2.2.2) summ_gen
  simp only [summ] at h
  exact h

/-- If `μ` has at most four rows and `x^{rows of μ}` appears in `X_G`, then `μ` is one of the
four shapes. -/
theorem chrom_support (μ : YoungDiagram) (h4 : (4, 0) ∉ μ)
    (h : coeff (rowVec μ) (chromSym G 4) ≠ 0) : μ = D0 ∨ μ = D1 ∨ μ = D2 ∨ μ = D3 := by
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
  rcases hok with ((h | h) | h) | h
  · left
    exact eq_ofRowLens μ h4 _ _ rfl fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · right; left
    exact eq_ofRowLens μ h4 _ _ rfl fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · right; right; left
    exact eq_ofRowLens μ h4 _ _ rfl fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · right; right; right
    exact eq_ofRowLens μ h4 _ _ rfl fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem D0_ne_D1 : D0 ≠ D1 := by
  intro h
  have : ((0, 4) : ℕ × ℕ) ∈ D0 := mem_ofRowLens_iff.mpr (by decide)
  rw [h] at this
  exact absurd (mem_ofRowLens_iff.mp this) (by decide)

theorem D0_ne_D2 : D0 ≠ D2 := by
  intro h
  have : ((0, 4) : ℕ × ℕ) ∈ D0 := mem_ofRowLens_iff.mpr (by decide)
  rw [h] at this
  exact absurd (mem_ofRowLens_iff.mp this) (by decide)

theorem D0_ne_D3 : D0 ≠ D3 := by
  intro h
  have : ((0, 4) : ℕ × ℕ) ∈ D0 := mem_ofRowLens_iff.mpr (by decide)
  rw [h] at this
  exact absurd (mem_ofRowLens_iff.mp this) (by decide)

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
  have key : ∀ μ ∈ s, c μ ≠ 0 → (4, 0) ∉ μ → μ = D0 ∨ μ = D1 ∨ μ = D2 ∨ μ = D3 := by
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
      ∑ μ ∈ ({D0, D1, D2, D3} : Finset YoungDiagram),
        (if μ ∈ s then (c μ : ℤ) else 0) * coeff α (schurPoly 4 μ) := by
    intro α
    rw [hco]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem]
    refine (Finset.sum_subset Finset.inter_subset_right fun μ hμs hμT => ?_).symm
    have hnT : μ ∉ ({D0, D1, D2, D3} : Finset YoungDiagram) :=
      fun hT => hμT (Finset.mem_inter.mpr ⟨hT, hμs⟩)
    by_cases hc : c μ = 0
    · simp [hc]
    by_cases h4 : (4, 0) ∈ μ
    · simp [schurPoly_eq_zero μ h4]
    exfalso
    apply hnT
    rcases key μ hμs hc h4 with rfl | rfl | rfl | rfl <;> simp
  have n0 : D0 ∉ ({D1, D2, D3} : Finset YoungDiagram) := by simp [D0_ne_D1, D0_ne_D2, D0_ne_D3]
  have n1 : D1 ∉ ({D2, D3} : Finset YoungDiagram) := by simp [D1_ne_D2, D1_ne_D3]
  have n2 : D2 ∉ ({D3} : Finset YoungDiagram) := by simp [D2_ne_D3]
  have E0 := hred e5322
  have E1 := hred e4422
  have E2 := hred e4332
  have E3 := hred e3333
  rw [Finset.sum_insert n0, Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_singleton]
    at E0 E1 E2 E3
  rw [K00, K10, K20, K30, chrom_5322] at E0
  rw [K01, K11, K21, K31, chrom_4422] at E1
  rw [K02, K12, K22, K32, chrom_4332] at E2
  rw [K03, K13, K23, K33, chrom_3333] at E3
  have h3 : (0 : ℤ) ≤ if D3 ∈ s then (c D3 : ℤ) else 0 := by split_ifs <;> positivity
  linarith

/-- **The claw-free Schur-positivity conjecture is false**, also witnessed by the second minimal
counterexample. -/
theorem not_clawFreeSchurPositivity : ¬ ClawFreeSchurPositivity :=
  fun h => not_schurPositive (h (Fin 12) G G_isClawFree 4)

end OpenProblemsLab.ClawFree.Second
