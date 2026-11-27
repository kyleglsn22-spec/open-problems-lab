import Mathlib

/-!
# Down-integers and up-integers of Chung–Graham–Spiro: basic theory

Chung, Graham and Spiro (slow Fibonacci walks) showed that every integer `n ≥ 2` has a unique
representation
`n = a f_t + b f_{t-1}` with `t ≥ 2` and `1 ≤ a ≤ b ≤ f_t` (`f_t` the Fibonacci numbers), and that
`n` is a *down-integer* (the slow walk to `n` continues with `⌊φ n⌋`) exactly when `t` is even, and an
*up-integer* (it continues with `⌈φ n⌉`) exactly when `t` is odd. Following Aliabadi
(arXiv:2609.04473), who works directly from this characterisation, we *define* down- and
up-integers by the parity of `t`.

This file proves, from scratch:
* `exists_rep`: every `n ≥ 2` has such a representation (so every `n ≥ 2` is a down- or an
  up-integer). Uniqueness is not needed anywhere below.
* `rep_delta_even`, `rep_delta_odd`: the fractional part `δ n = {φ n}` is `φ^{-t}(φ b - a)` for even
  `t` and `1 - φ^{-t}(φ b - a)` for odd `t`; with `0 < φ b - a < ρ φ^t`, `ρ = (2+φ)/5`, this gives
  `isDown → δ n < ρ` and `isUp → η < δ n` with `η = 1 - ρ` (Aliabadi's Lemma 1.2).
* `shift`: a general version of Aliabadi's forward-8 and backward-5 shift lemmas. If `n` is a
  down-integer with parameter `t ≥ j + 1` and `δ n ≥ θ_j`, then `n ± f_j` is again a down-integer
  (sign `+` for even `j`, `-` for odd `j`).
* `isDown_iff_downB`: a checkable Boolean description of down-integers below `377`.
-/

namespace OpenProblemsLab.FibWalk

open Nat (fib fib_add_two fib_pos le_fib_add_one nth)
open Real
open scoped goldenRatio

/-- A valid Chung–Graham–Spiro representation `n = a f_t + b f_{t-1}`, `t ≥ 2`,
`1 ≤ a ≤ b ≤ f_t`. -/
def IsRep (n t a b : ℕ) : Prop :=
  2 ≤ t ∧ 1 ≤ a ∧ a ≤ b ∧ b ≤ fib t ∧ n = a * fib t + b * fib (t - 1)

/-- Down-integers: representation parameter `t` even. -/
def IsDown (n : ℕ) : Prop := ∃ t a b, IsRep n t a b ∧ Even t

/-- Up-integers: representation parameter `t` odd. -/
def IsUp (n : ℕ) : Prop := ∃ t a b, IsRep n t a b ∧ Odd t

/-- The `ℓ`-step gap set `{x_{k+ℓ} - x_k}` of the increasing enumeration `x_0 < x_1 < ⋯` of
`{n | p n}` (`Nat.nth p k` is the `k`-th element, counting from `0`). -/
def gapSet (p : ℕ → Prop) (ℓ : ℕ) : Set ℕ := {g | ∃ k, nth p (k + ℓ) - nth p k = g}

/-! ### Existence of the representation -/

lemma IsRep.two_le {n t a b : ℕ} (h : IsRep n t a b) : 2 ≤ n := by
  obtain ⟨ht, ha, hab, -, rfl⟩ := h
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  have h1 : 1 ≤ fib (s + 2) := fib_pos.2 (by omega)
  have h2 : 1 ≤ fib (s + 2 - 1) := fib_pos.2 (by omega)
  nlinarith

theorem exists_rep {n : ℕ} (hn : 2 ≤ n) : ∃ t a b, IsRep n t a b := by
  classical
  let P : ℕ → Prop := fun t => 2 ≤ t ∧ ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ n = a * fib t + b * fib (t - 1)
  have hP2 : P 2 := ⟨le_rfl, 1, n - 1, le_rfl, by omega, by simp; omega⟩
  have hbound : ∀ t, P t → t ≤ n + 1 := by
    rintro t ⟨-, a, b, ha, -, rfl⟩
    have := le_fib_add_one t
    nlinarith
  have hPt : P (Nat.findGreatest P (n + 1)) := Nat.findGreatest_spec (hbound 2 hP2) hP2
  have hmax : ¬ P (Nat.findGreatest P (n + 1) + 1) := by
    intro h
    have := Nat.le_findGreatest (hbound _ h) h
    omega
  set t := Nat.findGreatest P (n + 1)
  obtain ⟨ht2, hex⟩ := hPt
  obtain ⟨s, hs⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  rw [hs] at hex hmax
  simp only [show s + 2 - 1 = s + 1 by omega] at hex
  let Q : ℕ → Prop := fun b => 1 ≤ b ∧ ∃ a, 1 ≤ a ∧ n = a * fib (s + 2) + b * fib (s + 1)
  have hQ : ∃ b, Q b := by
    obtain ⟨a, b, ha, hb, h⟩ := hex
    exact ⟨b, hb, a, ha, h⟩
  obtain ⟨hb1, a, ha1, hn'⟩ := Nat.find_spec hQ
  have hmin := fun m (hm : Q m) => Nat.find_min' hQ hm
  set b := Nat.find hQ
  refine ⟨s + 2, a, b, by omega, ha1, ?_, ?_, by simpa using hn'⟩
  · by_contra hab
    push Not at hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    apply hmax
    refine ⟨by omega, b, c + 1, hb1, by omega, ?_⟩
    simp only [show s + 2 + 1 - 1 = s + 2 by omega, show s + 2 + 1 = s + 3 by omega]
    rw [hn', fib_add_two (n := s + 1)]
    ring
  · by_contra hbt
    push Not at hbt
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt hbt
    have := hmin (c + 1) ⟨by omega, a + fib (s + 1), by omega, by rw [hn', hc]; ring⟩
    have : 1 ≤ fib (s + 2) := fib_pos.2 (by omega)
    omega

/-- Every `n ≥ 2` that is not a down-integer is an up-integer. -/
theorem isUp_of_not_isDown {n : ℕ} (hn : 2 ≤ n) (h : ¬ IsDown n) : IsUp n := by
  obtain ⟨t, a, b, hr⟩ := exists_rep hn
  exact ⟨t, a, b, hr, Nat.not_even_iff_odd.1 fun he => h ⟨t, a, b, hr, he⟩⟩

/-! ### The fractional part `δ n = {φ n}` -/

/-- `δ n = {φ n}`. -/
noncomputable def δ (n : ℕ) : ℝ := Int.fract (φ * n)

/-- `ρ = 1 - 1/(√5 φ) = (2 + φ)/5`. -/
noncomputable def ρ : ℝ := (2 + φ) / 5

/-- `η = 1/(√5 φ) = (3 - φ)/5 = 1 - ρ`. -/
noncomputable def η : ℝ := (3 - φ) / 5

lemma sqrt5_eq : √5 = 2 * φ - 1 := by rw [goldenRatio]; ring

lemma abs_psi_pow_le (m : ℕ) : |ψ ^ m| ≤ 1 := by
  rw [abs_pow]
  apply pow_le_one₀ (abs_nonneg _)
  rw [abs_le]
  constructor <;> linarith [neg_one_lt_goldenConj, goldenConj_neg]

lemma phi_bounds : (1.6180339 : ℝ) < φ ∧ φ < 1.618034 := by
  have h5 : (2.2360679 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h5' : √5 < (2.236068 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [goldenRatio]
  constructor <;> linarith

lemma phi_mul_fib (m : ℕ) : φ * fib m = fib (m + 1) - ψ ^ m := by
  linarith [fib_succ_sub_goldenRatio_mul_fib m]

lemma phi_mul_fib_lt (t : ℕ) : φ * fib t - 1 < ρ * φ ^ t := by
  have hb := coe_fib_eq t
  have hs : √5 = 2 * φ - 1 := sqrt5_eq
  have hpos : (0 : ℝ) < √5 := by positivity
  have h1 := abs_psi_pow_le t
  rw [abs_le] at h1
  have hp := phi_bounds
  have key : (fib t : ℝ) * √5 = φ ^ t - ψ ^ t := by rw [hb]; field_simp
  have hρ : ρ * √5 = φ := by
    rw [ρ, hs]; nlinarith [goldenRatio_sq]
  have : (φ * fib t - 1) * √5 < ρ * φ ^ t * √5 := by
    have e1 : (φ * fib t - 1) * √5 = φ * (φ ^ t - ψ ^ t) - √5 := by rw [← key]; ring
    have e2 : ρ * φ ^ t * √5 = φ * φ ^ t := by rw [mul_right_comm, hρ]
    rw [e1, e2]
    nlinarith
  exact lt_of_mul_lt_mul_right this hpos.le

/-- For a valid representation, `0 < φ b - a < ρ φ^t`. -/
lemma rep_Q_bounds {n t a b : ℕ} (h : IsRep n t a b) :
    0 < φ * b - a ∧ φ * b - a < ρ * φ ^ t := by
  obtain ⟨-, ha, hab, hbt, -⟩ := h
  have hp := phi_bounds
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbt' : (b : ℝ) ≤ fib t := by exact_mod_cast hbt
  constructor
  · nlinarith
  · have := phi_mul_fib_lt t
    nlinarith

/-- `φ n` splits as a natural number plus `E = -(a ψ^t + b ψ^{t-1})`. -/
lemma rep_phi_mul {n s a b : ℕ} (hn : n = a * fib (s + 2) + b * fib (s + 1)) :
    φ * n = ((a * fib (s + 3) + b * fib (s + 2) : ℕ) : ℝ) - (a * ψ ^ (s + 2) + b * ψ ^ (s + 1)) := by
  rw [hn]
  push_cast
  have e1 := phi_mul_fib (s + 2)
  have e2 := phi_mul_fib (s + 1)
  linear_combination (a : ℝ) * e1 + (b : ℝ) * e2

lemma psi_pow_mul_phi_pow (m : ℕ) : ψ ^ m * φ ^ m = (-1) ^ m := by
  rw [← mul_pow, goldenConj_mul_goldenRatio]

/-- Even parameter: `δ n · φ^t = φ b - a`. -/
lemma rep_delta_even {n t a b : ℕ} (h : IsRep n t a b) (he : Even t) :
    δ n * φ ^ t = φ * b - a := by
  have hQ := rep_Q_bounds h
  obtain ⟨ht, -, -, -, hn⟩ := h
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  simp only [show s + 2 - 1 = s + 1 by omega] at hn
  have hs : Odd (s + 1) := by
    rcases he with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
  have hpos : 0 < φ ^ (s + 2) := pow_pos goldenRatio_pos _
  -- E · φ^t = φ b - a
  have hE : -(a * ψ ^ (s + 2) + b * ψ ^ (s + 1)) * φ ^ (s + 2) = φ * b - a := by
    have h1 := psi_pow_mul_phi_pow (s + 2)
    have h2 := psi_pow_mul_phi_pow (s + 1)
    rw [Even.neg_one_pow he] at h1
    rw [Odd.neg_one_pow hs] at h2
    have : φ ^ (s + 2) = φ ^ (s + 1) * φ := pow_succ _ _
    rw [this] at h1 ⊢
    linear_combination (-(a : ℝ)) * h1 - (b : ℝ) * φ * h2
  have hρ : ρ < 1 := by rw [ρ]; linarith [phi_bounds.2]
  have hE0 : 0 < -(a * ψ ^ (s + 2) + b * ψ ^ (s + 1)) := by
    by_contra hc; push Not at hc; nlinarith
  have hE1 : -(a * ψ ^ (s + 2) + b * ψ ^ (s + 1)) < 1 := by
    by_contra hc; push Not at hc; nlinarith
  have : δ n = -(a * ψ ^ (s + 2) + b * ψ ^ (s + 1)) := by
    rw [δ, rep_phi_mul hn, Int.fract_eq_iff]
    refine ⟨hE0.le, hE1, (a * fib (s + 3) + b * fib (s + 2) : ℕ), ?_⟩
    push_cast; ring
  rw [this, hE]

/-- Odd parameter: `(1 - δ n) · φ^t = φ b - a`. -/
lemma rep_delta_odd {n t a b : ℕ} (h : IsRep n t a b) (ho : Odd t) :
    (1 - δ n) * φ ^ t = φ * b - a := by
  have hQ := rep_Q_bounds h
  have h2n := h.two_le
  obtain ⟨ht, ha, -, -, hn⟩ := h
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  simp only [show s + 2 - 1 = s + 1 by omega] at hn
  have hs : Even (s + 1) := by
    rcases ho with ⟨k, hk⟩; exact ⟨k, by omega⟩
  have hpos : 0 < φ ^ (s + 2) := pow_pos goldenRatio_pos _
  have hE : (a * ψ ^ (s + 2) + b * ψ ^ (s + 1)) * φ ^ (s + 2) = φ * b - a := by
    have h1 := psi_pow_mul_phi_pow (s + 2)
    have h2 := psi_pow_mul_phi_pow (s + 1)
    rw [Odd.neg_one_pow ho] at h1
    rw [Even.neg_one_pow hs] at h2
    have : φ ^ (s + 2) = φ ^ (s + 1) * φ := pow_succ _ _
    rw [this] at h1 ⊢
    linear_combination (a : ℝ) * h1 + (b : ℝ) * φ * h2
  have hρ : ρ < 1 := by rw [ρ]; linarith [phi_bounds.2]
  set E := a * ψ ^ (s + 2) + b * ψ ^ (s + 1) with hEdef
  have hE0 : 0 < E := by
    by_contra hc; push Not at hc; nlinarith
  have hE1 : E < 1 := by
    by_contra hc; push Not at hc; nlinarith
  have hM : 1 ≤ a * fib (s + 3) + b * fib (s + 2) := by
    have : 1 ≤ fib (s + 3) := fib_pos.2 (by omega)
    have : 1 ≤ a := by omega
    nlinarith
  have : δ n = 1 - E := by
    rw [δ, rep_phi_mul hn, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ((a * fib (s + 3) + b * fib (s + 2) - 1 : ℕ) : ℤ), ?_⟩
    push_cast [hM]; ring
  rw [this]; rw [← hE]; ring

lemma IsDown.delta_lt {n : ℕ} (h : IsDown n) : δ n < ρ := by
  obtain ⟨t, a, b, hr, he⟩ := h
  have e := rep_delta_even hr he
  have hQ := rep_Q_bounds hr
  have hpos : 0 < φ ^ t := pow_pos goldenRatio_pos _
  by_contra hc; push Not at hc; nlinarith

lemma IsUp.lt_delta {n : ℕ} (h : IsUp n) : η < δ n := by
  obtain ⟨t, a, b, hr, ho⟩ := h
  have e := rep_delta_odd hr ho
  have hQ := rep_Q_bounds hr
  have hpos : 0 < φ ^ t := pow_pos goldenRatio_pos _
  have : η = 1 - ρ := by rw [η, ρ]; ring
  rw [this]
  by_contra hc; push Not at hc; nlinarith

/-! ### Shift lemmas -/

/-- If `√5 (φ b - a) ≥ φ^s + φ^m` for a valid representation with `t = s + 1`, then
`b - a ≥ f_m`. -/
lemma gap_of_Q {n s m a b : ℕ} (h : IsRep n (s + 1) a b)
    (hQ : φ ^ s + φ ^ m ≤ √5 * (φ * b - a)) : a + fib m ≤ b := by
  obtain ⟨-, ha, hab, hbt, -⟩ := h
  have hbt' : (b : ℝ) ≤ fib (s + 1) := by exact_mod_cast hbt
  have hs : √5 = 2 * φ - 1 := sqrt5_eq
  have hp := phi_bounds
  have k1 : (fib (s + 1) : ℝ) * √5 = φ ^ (s + 1) - ψ ^ (s + 1) := by
    rw [coe_fib_eq]; field_simp
  have k2 : (fib m : ℝ) * √5 = φ ^ m - ψ ^ m := by
    rw [coe_fib_eq]; field_simp
  have a1 := abs_psi_pow_le (s + 1)
  have a2 := abs_psi_pow_le m
  rw [abs_le] at a1 a2
  have hφs : (φ - 1) * φ ^ (s + 1) = φ ^ s := by
    rw [pow_succ]; linear_combination φ ^ s * goldenRatio_sq
  -- (b - a) √5 > (f_m - 1) √5
  have key : ((fib m : ℝ) - 1) * √5 < ((b : ℝ) - a) * √5 := by
    have : ((b : ℝ) - a) * √5 = √5 * (φ * b - a) - (φ - 1) * √5 * b := by ring
    rw [this]
    have hb0 : (0 : ℝ) ≤ b := by positivity
    have : (φ - 1) * √5 * b ≤ (φ - 1) * √5 * fib (s + 1) := by
      apply mul_le_mul_of_nonneg_left hbt'; rw [hs]; nlinarith
    have e3 : (φ - 1) * √5 * fib (s + 1) = φ ^ s - (φ - 1) * ψ ^ (s + 1) := by
      rw [mul_assoc, mul_comm √5, k1]; linear_combination hφs
    have e4 : ((fib m : ℝ) - 1) * √5 = φ ^ m - ψ ^ m - √5 := by rw [sub_mul, k2]; ring
    rw [e4]
    nlinarith
  have hpos : (0 : ℝ) < √5 := by positivity
  have : (fib m : ℝ) - 1 < (b : ℝ) - a := lt_of_mul_lt_mul_right key hpos.le
  have : (fib m : ℤ) - 1 < (b : ℤ) - a := by exact_mod_cast this
  omega

/-- d'Ocagne-type identity: `f_r f_{r+j+1} - f_{r+1} f_{r+j} = (-1)^{r+1} f_j`. -/
lemma fib_shift_identity (j : ℕ) : ∀ r : ℕ,
    (fib r * fib (r + j + 1) : ℤ) - fib (r + 1) * fib (r + j) = (-1) ^ (r + 1) * fib j
  | 0 => by simp
  | r + 1 => by
    have ih := fib_shift_identity j r
    have e1 : fib (r + j + 1 + 1) = fib (r + j) + fib (r + j + 1) := fib_add_two
    have e2 : fib (r + 1 + 1) = fib r + fib (r + 1) := fib_add_two
    rw [show r + 1 + j = r + j + 1 by omega, e1, e2]
    push_cast
    rw [pow_succ]
    linear_combination -ih

/-- The shift: from a valid representation with `t = r + j + 1` and `b - a ≥ f_{r+2}`, the number
`n + (-1)^{r+1} f_j` has the valid representation `(a + f_r, b - f_{r+1})` with the same `t`. -/
lemma rep_shift {n r j a b : ℕ} (h : IsRep n (r + j + 1) a b) (hg : a + fib (r + 2) ≤ b) :
    ∃ n' : ℕ, (n' : ℤ) = n + (-1) ^ (r + 1) * fib j ∧
      IsRep n' (r + j + 1) (a + fib r) (b - fib (r + 1)) := by
  obtain ⟨ht, ha, hab, hbt, hn⟩ := h
  have hf2 : fib (r + 2) = fib r + fib (r + 1) := fib_add_two
  refine ⟨(a + fib r) * fib (r + j + 1) + (b - fib (r + 1)) * fib (r + j + 1 - 1), ?_,
    ht, by omega, by omega, by omega, rfl⟩
  have id := fib_shift_identity j r
  simp only [show r + j + 1 - 1 = r + j by omega] at hn ⊢
  rw [hn]
  push_cast [show fib (r + 1) ≤ b by omega]
  linear_combination id

/-- **General shift lemma.** Let `n` be a down-integer with even parameter `t ≥ j + 1`, `j ≥ 2`,
and let `θ` satisfy `θ √5 φ^{j-1} = φ^{j-2} + 1`. If `δ n ≥ θ` then `n + (-1)^{t-j} f_j` is a
down-integer. -/
theorem shift {n t a b j : ℕ} (θ : ℝ) (hj : 2 ≤ j) (hθ : θ * √5 * φ ^ (j - 1) = φ ^ (j - 2) + 1)
    (h : IsRep n t a b) (he : Even t) (ht : j + 1 ≤ t) (hδ : θ ≤ δ n) :
    ∃ n' : ℕ, (n' : ℤ) = n + (-1) ^ (t - j) * fib j ∧ IsDown n' := by
  obtain ⟨r, rfl⟩ : ∃ r, t = r + j + 1 := ⟨t - j - 1, by omega⟩
  have e := rep_delta_even h he
  have hg : a + fib (r + 2) ≤ b := by
    apply gap_of_Q (s := r + j) (n := n) h
    have hpos : 0 < φ ^ (r + 2) := pow_pos goldenRatio_pos _
    have hs5 : (0 : ℝ) ≤ √5 := by positivity
    have p1 : φ ^ (r + j + 1) = φ ^ (j - 1) * φ ^ (r + 2) := by
      rw [← pow_add]; congr 1; omega
    have p2 : φ ^ (r + j) = φ ^ (j - 2) * φ ^ (r + 2) := by
      rw [← pow_add]; congr 1; omega
    rw [← e, p1, p2]
    have : θ * √5 * φ ^ (j - 1) * φ ^ (r + 2) ≤ δ n * √5 * φ ^ (j - 1) * φ ^ (r + 2) := by
      have : 0 ≤ √5 * φ ^ (j - 1) * φ ^ (r + 2) := by positivity
      nlinarith
    rw [hθ] at this
    linarith
  obtain ⟨n', hn', hr'⟩ := rep_shift h hg
  exact ⟨n', by rw [hn', show r + j + 1 - j = r + 1 by omega], _, _, _, hr', he⟩

/-! ### The five thresholds -/

/-- `θ₂ = (6 - 2φ)/5`, for the shift `+1`. -/
noncomputable def θ₂ : ℝ := (6 - 2 * φ) / 5
/-- `θ₃ = (2φ - 1)/5 = 1/√5`, for the shift `-2`. -/
noncomputable def θ₃ : ℝ := (2 * φ - 1) / 5
/-- `θ₄ = 2 - φ`, for the shift `+3`. -/
noncomputable def θ₄ : ℝ := 2 - φ
/-- `θ₅ = (6φ - 8)/5`, for the shift `-5`. -/
noncomputable def θ₅ : ℝ := (6 * φ - 8) / 5
/-- `θ₆ = (21 - 12φ)/5`, for the shift `+8`. -/
noncomputable def θ₆ : ℝ := (21 - 12 * φ) / 5

lemma hθ₂ : θ₂ * √5 * φ ^ (2 - 1) = φ ^ (2 - 2) + 1 := by
  show θ₂ * √5 * φ ^ 1 = φ ^ 0 + 1
  rw [θ₂, sqrt5_eq]; linear_combination (2 - 4 * φ / 5) * goldenRatio_sq
lemma hθ₃ : θ₃ * √5 * φ ^ (3 - 1) = φ ^ (3 - 2) + 1 := by
  show θ₃ * √5 * φ ^ 2 = φ ^ 1 + 1
  rw [θ₃, sqrt5_eq]; linear_combination (4 * φ ^ 2 / 5 + 1) * goldenRatio_sq
lemma hθ₄ : θ₄ * √5 * φ ^ (4 - 1) = φ ^ (4 - 2) + 1 := by
  show θ₄ * √5 * φ ^ 3 = φ ^ 2 + 1
  rw [θ₄, sqrt5_eq]; linear_combination (-2 * φ ^ 3 + 3 * φ ^ 2 - φ + 1) * goldenRatio_sq
lemma hθ₅ : θ₅ * √5 * φ ^ (5 - 1) = φ ^ (5 - 2) + 1 := by
  show θ₅ * √5 * φ ^ 4 = φ ^ 3 + 1
  rw [θ₅, sqrt5_eq]; linear_combination (12 * φ ^ 4 / 5 - 2 * φ ^ 3 + 2 * φ ^ 2 - φ + 1) * goldenRatio_sq
lemma hθ₆ : θ₆ * √5 * φ ^ (6 - 1) = φ ^ (6 - 2) + 1 := by
  show θ₆ * √5 * φ ^ 5 = φ ^ 4 + 1
  rw [θ₆, sqrt5_eq]; linear_combination (-24 * φ ^ 5 / 5 + 6 * φ ^ 4 - 3 * φ ^ 3 + 2 * φ ^ 2 - φ + 1) * goldenRatio_sq

end OpenProblemsLab.FibWalk
