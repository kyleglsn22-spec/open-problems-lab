import Mathlib

/-!
# The Hinrichs–Vybíral conjecture on positive definite functions is false

A function `f : ℝ^d → ℝ` is positive definite if every matrix `[f(x_j − x_k)]` is positive
semidefinite (as a Hermitian matrix: `∑ c_j c̄_k f(x_j − x_k) ≥ 0` for complex `c`). Hinrichs and
Vybíral (*On positive positive-definite functions and Bochner's theorem*, J. Complexity 27 (2011),
Conjecture 2) conjectured that if such an `f` is also continuous, bounded, nonnegative and
`f(0) = 1`, then `[f(x_j − x_k)] ⪰ (1/n) J_n` for all points `x_1, …, x_n`. In particular, for
real coefficients, `∑ c_j c_k f(x_j − x_k) ≥ (∑ c_j)² / n`.

J. Vybíral (arXiv:2609.21733) gives an explicit counterexample in dimension `7`:
`f(x) = P(cos x₁, …, cos x₇)` with `P = (21 + 4E₂ + 4E₃ + E₄)/280`, where `E_r` are the elementary
symmetric polynomials. At the `8` points `0, πe₁, …, πe₇` with coefficients `−1, 1, …, 1`, the
quadratic form is `22/5`, below `(∑ c)²/8 = 9/2`.

We write `f(x) = (1/280) ∑_S w(|S|) ∏_{ℓ ∈ S} cos x_ℓ` over subsets `S ⊆ {1, …, 7}`, with
`w = (21, 0, 4, 4, 1, 0, 0, 0)`.

* Positive definite: `∏_{ℓ ∈ S} cos(a_ℓ − b_ℓ) = ∑_{t ⊆ S} φ_t(a) φ_t(b)` with
  `φ_t(a) = ∏_{t} cos a_ℓ · ∏_{S∖t} sin a_ℓ` (expand `cos(a − b)`), so the form is a nonnegative
  combination of terms `|∑_j c_j φ_t(x_j)|²`.
* Nonnegative: `P` is affine in each variable, so on `[−1, 1]^7` it is a convex combination of its
  values at the `128` sign vectors, which are all `≥ 0` (checked by `decide`).

Main result: `not_hinrichsVybiralConjecture`.
-/

namespace OpenProblemsLab.HinrichsVybiral

open Finset Real
open scoped ComplexOrder

/-- `f` is positive definite: every matrix `[f(x_j − x_k)]` is positive semidefinite (Hermitian form,
complex coefficients). -/
def IsPosDef {d : ℕ} (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → Fin d → ℝ) (c : Fin n → ℂ),
    0 ≤ ∑ j, ∑ k, c j * star (c k) * (f (x j - x k) : ℂ)

/-- **Hinrichs–Vybíral conjecture** (real-coefficient consequence of `[f(x_j − x_k)] ⪰ J_n / n`):
every continuous, bounded, nonnegative, positive definite `f` with `f(0) = 1` satisfies
`∑ c_j c_k f(x_j − x_k) ≥ (∑ c_j)² / n`. -/
def HinrichsVybiralConjecture : Prop :=
  ∀ (d : ℕ) (f : (Fin d → ℝ) → ℝ), Continuous f → (∃ M, ∀ x, |f x| ≤ M) → (∀ x, 0 ≤ f x) →
    f 0 = 1 → IsPosDef f →
    ∀ (n : ℕ) (x : Fin n → Fin d → ℝ) (c : Fin n → ℝ),
      (∑ j, c j) ^ 2 / n ≤ ∑ j, ∑ k, c j * c k * f (x j - x k)

/-! ## Vybíral's function -/

/-- Weights `280 · (coefficient of E_r)`. -/
def w (r : ℕ) : ℤ := [21, 0, 4, 4, 1, 0, 0, 0].getD r 0

theorem w_nonneg (r : ℕ) : 0 ≤ w r := by
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> simp [w]

/-- The multiaffine polynomial `280 · P`. -/
noncomputable def g (y : Fin 7 → ℝ) : ℝ := ∑ S : Finset (Fin 7), (w S.card : ℝ) * ∏ ℓ ∈ S, y ℓ

/-- Vybíral's function `f(x) = P(cos x₁, …, cos x₇)`. -/
noncomputable def f (x : Fin 7 → ℝ) : ℝ := g (fun ℓ => cos (x ℓ)) / 280

/-- `280 · P` at a sign vector (`true` means `−1`), as an integer. -/
def G (b : Fin 7 → Bool) : ℤ := ∑ S : Finset (Fin 7), w S.card * ∏ ℓ ∈ S, (if b ℓ then -1 else 1)

theorem g_sign (b : Fin 7 → Bool) : g (fun ℓ => if b ℓ then -1 else 1) = (G b : ℝ) := by
  unfold g G
  push_cast
  refine sum_congr rfl fun S _ => ?_
  congr 1

theorem G_nonneg : ∀ b : Fin 7 → Bool, 0 ≤ G b := by decide +kernel

/-! ### Nonnegativity -/

/-- `g` is affine in each coordinate. -/
theorem g_affine (y : Fin 7 → ℝ) (i : Fin 7) :
    g y = (1 + y i) / 2 * g (Function.update y i 1) + (1 - y i) / 2 * g (Function.update y i (-1)) := by
  unfold g
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun S _ => ?_
  by_cases hi : i ∈ S
  · rw [← mul_prod_erase S _ hi, ← mul_prod_erase S _ hi, ← mul_prod_erase S _ hi]
    have h1 : ∏ ℓ ∈ S.erase i, Function.update y i 1 ℓ = ∏ ℓ ∈ S.erase i, y ℓ :=
      prod_congr rfl fun ℓ hℓ => Function.update_of_ne (ne_of_mem_erase hℓ) _ _
    have h2 : ∏ ℓ ∈ S.erase i, Function.update y i (-1) ℓ = ∏ ℓ ∈ S.erase i, y ℓ :=
      prod_congr rfl fun ℓ hℓ => Function.update_of_ne (ne_of_mem_erase hℓ) _ _
    rw [h1, h2]
    simp only [Function.update_self]
    ring
  · have h1 : ∏ ℓ ∈ S, Function.update y i 1 ℓ = ∏ ℓ ∈ S, y ℓ :=
      prod_congr rfl fun ℓ hℓ => Function.update_of_ne (fun h => hi (by rw [← h]; exact hℓ)) _ _
    have h2 : ∏ ℓ ∈ S, Function.update y i (-1) ℓ = ∏ ℓ ∈ S, y ℓ :=
      prod_congr rfl fun ℓ hℓ => Function.update_of_ne (fun h => hi (by rw [← h]; exact hℓ)) _ _
    rw [h1, h2]
    ring

theorem g_nonneg_aux (s : Finset (Fin 7)) : ∀ y : Fin 7 → ℝ, (∀ i, |y i| ≤ 1) →
    (∀ i ∉ s, y i = 1 ∨ y i = -1) → 0 ≤ g y := by
  induction s using Finset.induction_on with
  | empty =>
    intro y _ hy
    have hy' : y = fun ℓ => if decide (y ℓ = -1) then -1 else 1 := by
      funext ℓ
      rcases hy ℓ (notMem_empty ℓ) with h | h <;> simp [h]
    rw [hy', g_sign]
    exact_mod_cast G_nonneg _
  | insert i s _ ih =>
    intro y hb hy
    rw [g_affine y i]
    have hyi := abs_le.mp (hb i)
    have hupd : ∀ v : ℝ, (v = 1 ∨ v = -1) → 0 ≤ g (Function.update y i v) := by
      intro v hv
      apply ih
      · intro j
        by_cases hj : j = i
        · subst hj; rcases hv with rfl | rfl <;> simp
        · rw [Function.update_of_ne hj]; exact hb j
      · intro j hj
        by_cases hji : j = i
        · subst hji; simpa using hv
        · rw [Function.update_of_ne hji]; exact hy j (by simp [hji, hj])
    have := hupd 1 (Or.inl rfl)
    have := hupd (-1) (Or.inr rfl)
    have : 0 ≤ (1 + y i) / 2 := by linarith
    have : 0 ≤ (1 - y i) / 2 := by linarith
    positivity

theorem f_nonneg (x : Fin 7 → ℝ) : 0 ≤ f x := by
  unfold f
  apply div_nonneg _ (by norm_num)
  exact g_nonneg_aux univ _ (fun i => abs_cos_le_one _) (fun i hi => absurd (mem_univ i) hi)

/-! ### Positive definiteness -/

/-- Feature functions `φ_{S,t}(a) = ∏_{t} cos a_ℓ · ∏_{S∖t} sin a_ℓ`. -/
noncomputable def φ (S t : Finset (Fin 7)) (a : Fin 7 → ℝ) : ℝ :=
  (∏ ℓ ∈ t, cos (a ℓ)) * ∏ ℓ ∈ S \ t, sin (a ℓ)

theorem prod_cos_sub (S : Finset (Fin 7)) (a b : Fin 7 → ℝ) :
    ∏ ℓ ∈ S, cos (a ℓ - b ℓ) = ∑ t ∈ S.powerset, φ S t a * φ S t b := by
  simp_rw [cos_sub]
  rw [prod_add]
  refine sum_congr rfl fun t _ => ?_
  unfold φ
  rw [prod_mul_distrib, prod_mul_distrib]
  ring

theorem f_sub (a b : Fin 7 → ℝ) :
    f (a - b) = ∑ S : Finset (Fin 7), ∑ t ∈ S.powerset, (w S.card : ℝ) / 280 * (φ S t a * φ S t b) := by
  unfold f g
  simp only [Pi.sub_apply, prod_cos_sub, sum_div, mul_sum]
  refine sum_congr rfl fun S _ => sum_congr rfl fun t _ => ?_
  ring

theorem f_posDef : IsPosDef f := by
  intro n x c
  let A : Finset (Fin 7) → ℂ := fun S => (((w S.card : ℝ) / 280 : ℝ) : ℂ)
  let u : Finset (Fin 7) → Finset (Fin 7) → Fin n → ℂ := fun S t j => c j * (φ S t (x j) : ℂ)
  let F : Finset (Fin 7) → Finset (Fin 7) → Fin n → Fin n → ℂ :=
    fun S t j k => A S * (u S t j * star (u S t k))
  have step1 : ∀ j k, c j * star (c k) * (f (x j - x k) : ℂ) =
      ∑ S : Finset (Fin 7), ∑ t ∈ S.powerset, F S t j k := by
    intro j k
    rw [f_sub]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun S _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun t _ => ?_
    simp only [F, A, u, star_mul', Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  have step2 : ∑ j, ∑ k, c j * star (c k) * (f (x j - x k) : ℂ) =
      ∑ S : Finset (Fin 7), ∑ t ∈ S.powerset, A S * ((∑ j, u S t j) * star (∑ k, u S t k)) := by
    simp_rw [step1]
    calc ∑ j, ∑ k, ∑ S : Finset (Fin 7), ∑ t ∈ S.powerset, F S t j k
        = ∑ j, ∑ S : Finset (Fin 7), ∑ k, ∑ t ∈ S.powerset, F S t j k :=
          sum_congr rfl fun j _ => sum_comm
      _ = ∑ S : Finset (Fin 7), ∑ j, ∑ k, ∑ t ∈ S.powerset, F S t j k := sum_comm
      _ = ∑ S : Finset (Fin 7), ∑ j, ∑ t ∈ S.powerset, ∑ k, F S t j k :=
          sum_congr rfl fun S _ => sum_congr rfl fun j _ => sum_comm
      _ = ∑ S : Finset (Fin 7), ∑ t ∈ S.powerset, ∑ j, ∑ k, F S t j k :=
          sum_congr rfl fun S _ => sum_comm
      _ = _ := by
          refine sum_congr rfl fun S _ => sum_congr rfl fun t _ => ?_
          rw [star_sum, sum_mul_sum, mul_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [mul_sum]
  rw [step2]
  refine sum_nonneg fun S _ => sum_nonneg fun t _ => ?_
  apply mul_nonneg
  · have : (0 : ℝ) ≤ (w S.card : ℝ) / 280 := div_nonneg (by exact_mod_cast w_nonneg _) (by norm_num)
    exact Complex.zero_le_real.mpr this
  · exact mul_star_self_nonneg _

/-! ### The other hypotheses -/

theorem f_continuous : Continuous f := by
  unfold f g
  fun_prop

theorem f_bounded : ∃ M, ∀ x, |f x| ≤ M := by
  refine ⟨∑ S : Finset (Fin 7), (w S.card : ℝ) / 280, fun x => ?_⟩
  unfold f g
  rw [sum_div, abs_le]
  constructor
  · have := f_nonneg x
    unfold f g at this
    rw [sum_div] at this
    have h0 : (0 : ℝ) ≤ ∑ S : Finset (Fin 7), (w S.card : ℝ) / 280 :=
      sum_nonneg fun S _ => div_nonneg (by exact_mod_cast w_nonneg _) (by norm_num)
    linarith
  · refine sum_le_sum fun S _ => ?_
    have hw : (0 : ℝ) ≤ w S.card := by exact_mod_cast w_nonneg _
    have hp : ∏ ℓ ∈ S, cos (x ℓ) ≤ 1 := by
      calc ∏ ℓ ∈ S, cos (x ℓ) ≤ |∏ ℓ ∈ S, cos (x ℓ)| := le_abs_self _
        _ = ∏ ℓ ∈ S, |cos (x ℓ)| := abs_prod _ _
        _ ≤ ∏ ℓ ∈ S, (1 : ℝ) :=
          prod_le_prod (fun _ _ => abs_nonneg _) (fun _ _ => abs_cos_le_one _)
        _ = 1 := prod_const_one
    rw [div_le_div_iff_of_pos_right (by norm_num)]
    calc (w S.card : ℝ) * ∏ ℓ ∈ S, cos (x ℓ) ≤ (w S.card : ℝ) * 1 := mul_le_mul_of_nonneg_left hp hw
      _ = w S.card := mul_one _

/-! ### The violation -/

/-- Which coordinate axis a point sits on: point `0` is the origin, point `j + 1` is `π e_j`. -/
def pos (j : Fin 8) : Option (Fin 7) := if h : j.val = 0 then none else some ⟨j.val - 1, by omega⟩

/-- The eight points. -/
noncomputable def pts (j : Fin 8) : Fin 7 → ℝ := fun ℓ => if pos j = some ℓ then π else 0

/-- The coefficients `−1, 1, …, 1`. -/
def coef (j : Fin 8) : ℤ := if j.val = 0 then -1 else 1

/-- The sign pattern of `cos (pts j − pts k)`. -/
def sgn (j k : Fin 8) (ℓ : Fin 7) : Bool := xor (decide (pos j = some ℓ)) (decide (pos k = some ℓ))

theorem cos_pts (j k : Fin 8) (ℓ : Fin 7) :
    cos (pts j ℓ - pts k ℓ) = if sgn j k ℓ then -1 else 1 := by
  unfold pts sgn
  by_cases h1 : pos j = some ℓ <;> by_cases h2 : pos k = some ℓ <;> simp [h1, h2]

theorem f_pts (j k : Fin 8) : f (pts j - pts k) = (G (sgn j k) : ℝ) / 280 := by
  unfold f
  simp only [Pi.sub_apply, cos_pts]
  rw [g_sign]

theorem form_eq : ∑ j : Fin 8, ∑ k : Fin 8, coef j * coef k * G (sgn j k) = 1232 := by decide +kernel

theorem coef_sum : ∑ j : Fin 8, coef j = 6 := by decide +kernel

/-- **The Hinrichs–Vybíral conjecture is false.** -/
theorem not_hinrichsVybiralConjecture : ¬ HinrichsVybiralConjecture := by
  intro h
  have h0 : f 0 = 1 := by
    have : (0 : Fin 7 → ℝ) = pts 0 - pts 0 := by simp
    rw [this, f_pts]
    have : G (sgn 0 0) = 280 := by decide +kernel
    rw [this]; norm_num
  have := h 7 f f_continuous f_bounded f_nonneg h0 f_posDef 8 pts (fun j => (coef j : ℝ))
  simp only [f_pts] at this
  have e1 : ∑ j : Fin 8, ∑ k : Fin 8, (coef j : ℝ) * (coef k : ℝ) * ((G (sgn j k) : ℝ) / 280) =
      (1232 : ℝ) / 280 := by
    have hf : (∑ j : Fin 8, ∑ k : Fin 8, (coef j : ℝ) * coef k * G (sgn j k)) = 1232 := by
      exact_mod_cast form_eq
    rw [← hf, sum_div]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun k _ => ?_
    ring
  have e2 : ∑ j : Fin 8, (coef j : ℝ) = 6 := by exact_mod_cast coef_sum
  rw [e1, e2] at this
  norm_num at this

end OpenProblemsLab.HinrichsVybiral
