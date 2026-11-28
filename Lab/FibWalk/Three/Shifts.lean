import Lab.FibWalk.Main

/-!
# Shift lemmas for up-integers, and gap-set bookkeeping

This file mirrors the shift lemma of `Basic.lean` for up-integers. For odd `t` we have
`(1 - δ n) φ^t = φ b - a`, so the same argument gives the following. An up-integer `n` with
`1 - δ n ≥ θ_j` moves to the up-integer `n + (-1)^{t-j} f_j`, which is `n - (-1)^j f_j`.

It also proves two facts about `Nat.nth`: the member after `nth p k` is at most any later member, and nothing strictly between consecutive members belongs to `p`.
-/

namespace OpenProblemsLab.FibWalk

open Nat (fib fib_pos fib_add_two count nth)
open Real
open scoped goldenRatio Classical

/-- Every `n ≥ 2` that is not an up-integer is a down-integer. -/
theorem isDown_of_not_isUp {n : ℕ} (hn : 2 ≤ n) (h : ¬ IsUp n) : IsDown n := by
  obtain ⟨t, a, b, hr⟩ := exists_rep hn
  exact ⟨t, a, b, hr, Nat.not_odd_iff_even.1 fun ho => h ⟨t, a, b, hr, ho⟩⟩

/-- **Shift lemma for up-integers.** Let `n` be an up-integer with odd parameter `t ≥ j + 1`,
`j ≥ 2`, and let `θ` satisfy `θ √5 φ^{j-1} = φ^{j-2} + 1`. If `1 - δ n ≥ θ` then
`n + (-1)^{t-j} f_j` is an up-integer. -/
theorem shift_up {n t a b j : ℕ} (θ : ℝ) (hj : 2 ≤ j) (hθ : θ * √5 * φ ^ (j - 1) = φ ^ (j - 2) + 1)
    (h : IsRep n t a b) (ho : Odd t) (ht : j + 1 ≤ t) (hδ : θ ≤ 1 - δ n) :
    ∃ n' : ℕ, (n' : ℤ) = n + (-1) ^ (t - j) * fib j ∧ IsUp n' := by
  obtain ⟨r, rfl⟩ : ∃ r, t = r + j + 1 := ⟨t - j - 1, by omega⟩
  have e := rep_delta_odd h ho
  have hg : a + fib (r + 2) ≤ b := by
    apply gap_of_Q (s := r + j) (n := n) h
    have hpos : 0 < φ ^ (r + 2) := pow_pos goldenRatio_pos _
    have hs5 : (0 : ℝ) ≤ √5 := by positivity
    have p1 : φ ^ (r + j + 1) = φ ^ (j - 1) * φ ^ (r + 2) := by
      rw [← pow_add]; congr 1; omega
    have p2 : φ ^ (r + j) = φ ^ (j - 2) * φ ^ (r + 2) := by
      rw [← pow_add]; congr 1; omega
    rw [← e, p1, p2]
    have : θ * √5 * φ ^ (j - 1) * φ ^ (r + 2) ≤ (1 - δ n) * √5 * φ ^ (j - 1) * φ ^ (r + 2) := by
      have : 0 ≤ √5 * φ ^ (j - 1) * φ ^ (r + 2) := by positivity
      nlinarith
    rw [hθ] at this
    linarith
  obtain ⟨n', hn', hr'⟩ := rep_shift h hg
  exact ⟨n', by rw [hn', show r + j + 1 - j = r + 1 by omega], _, _, _, hr', ho⟩

/-- Up-integers `≥ 41` have representation parameter `t ≥ 7`. -/
lemma seven_le_of_rep_odd {N t a b : ℕ} (h : IsRep N t a b) (ho : Odd t) (hN : 41 ≤ N) : 7 ≤ t := by
  by_contra h7
  obtain ⟨ht, -, hab, hbt, rfl⟩ := h
  have hb : a * fib t + b * fib (t - 1) ≤ fib t * fib t + fib t * fib (t - 1) := by
    have : a ≤ fib t := by omega
    exact Nat.add_le_add (Nat.mul_le_mul_right _ this) (Nat.mul_le_mul_right _ hbt)
  have : t = 3 ∨ t = 5 := by
    obtain ⟨k, hk⟩ := ho; omega
  rcases this with rfl | rfl <;>
    simp only [show fib 3 = 2 from rfl, show fib 5 = 5 from rfl,
      show fib (3 - 1) = 1 from rfl, show fib (5 - 1) = 3 from rfl] at hb hN <;>
    omega

/-- The shift lemma for an up-integer `N ≥ 41`, with the sign written as `-(-1)^j`. -/
lemma shift_up' {N j : ℕ} (θ : ℝ) (hj : 2 ≤ j) (hj6 : j ≤ 6)
    (hθ : θ * √5 * φ ^ (j - 1) = φ ^ (j - 2) + 1) (hN : 41 ≤ N) (h : IsUp N) (hδ : δ N ≤ 1 - θ) :
    ∃ n' : ℕ, (n' : ℤ) = N - (-1) ^ j * fib j ∧ IsUp n' := by
  obtain ⟨t, a, b, hr, ho⟩ := h
  have ht := seven_le_of_rep_odd hr ho hN
  obtain ⟨n', hn', hd⟩ := shift_up θ hj hθ hr ho (by omega) (by linarith)
  refine ⟨n', ?_, hd⟩
  rw [hn', sub_eq_add_neg, ← neg_mul]
  congr 2
  rcases Nat.even_or_odd j with hje | hjo
  · have : Odd (t - j) := by
      rcases ho with ⟨k, hk⟩; rcases hje with ⟨i, hi⟩; exact ⟨k - i, by omega⟩
    rw [hje.neg_one_pow, this.neg_one_pow]
  · have : Even (t - j) := by
      rcases ho with ⟨k, hk⟩; rcases hjo with ⟨i, hi⟩; exact ⟨k - i, by omega⟩
    rw [hjo.neg_one_pow, this.neg_one_pow, neg_neg]

lemma up_minus1 {N : ℕ} (hN : 41 ≤ N) (h : IsUp N) (hδ : δ N ≤ 1 - θ₂) : IsUp (N - 1) := by
  obtain ⟨n', hn', hd⟩ := shift_up' θ₂ le_rfl (by norm_num) hθ₂ hN h hδ
  have : n' = N - 1 := by norm_num [Nat.fib] at hn'; omega
  rwa [this] at hd

lemma up_plus2 {N : ℕ} (hN : 41 ≤ N) (h : IsUp N) (hδ : δ N ≤ 1 - θ₃) : IsUp (N + 2) := by
  obtain ⟨n', hn', hd⟩ := shift_up' θ₃ (by norm_num) (by norm_num) hθ₃ hN h hδ
  have : n' = N + 2 := by norm_num [Nat.fib] at hn'; omega
  rwa [this] at hd

lemma up_minus3 {N : ℕ} (hN : 41 ≤ N) (h : IsUp N) (hδ : δ N ≤ 1 - θ₄) : IsUp (N - 3) := by
  obtain ⟨n', hn', hd⟩ := shift_up' θ₄ (by norm_num) (by norm_num) hθ₄ hN h hδ
  have : n' = N - 3 := by norm_num [Nat.fib] at hn'; omega
  rwa [this] at hd

lemma up_plus5 {N : ℕ} (hN : 41 ≤ N) (h : IsUp N) (hδ : δ N ≤ 1 - θ₅) : IsUp (N + 5) := by
  obtain ⟨n', hn', hd⟩ := shift_up' θ₅ (by norm_num) (by norm_num) hθ₅ hN h hδ
  have : n' = N + 5 := by norm_num [Nat.fib] at hn'; omega
  rwa [this] at hd

lemma up_minus8 {N : ℕ} (hN : 41 ≤ N) (h : IsUp N) (hδ : δ N ≤ 1 - θ₆) : IsUp (N - 8) := by
  obtain ⟨n', hn', hd⟩ := shift_up' θ₆ (by norm_num) (by norm_num) hθ₆ hN h hδ
  have : n' = N - 8 := by norm_num [Nat.fib] at hn'; omega
  rwa [this] at hd

/-! ### Gap sets as windows -/

section nth

variable {p : ℕ → Prop} [DecidablePred p]

/-- The element after `nth p k` is at most any later member of `p`. -/
lemma nth_succ_le (hinf : (Set.ofPred p).Infinite) {k m : ℕ} (hm : p m) (hlt : nth p k < m) :
    nth p (k + 1) ≤ m := by
  have h1 : count p (nth p k + 1) = k + 1 := by
    rw [Nat.count_succ, Nat.count_nth_of_infinite hinf, if_pos (Nat.nth_mem_of_infinite hinf k)]
  have h2 : k + 1 ≤ count p m := h1 ▸ Nat.count_monotone p hlt
  calc nth p (k + 1) ≤ nth p (count p m) := Nat.nth_monotone hinf h2
    _ = m := Nat.nth_count hm

/-- Nothing strictly between two consecutive members is a member. -/
lemma not_mem_between (hinf : (Set.ofPred p).Infinite) {k m : ℕ} (h1 : nth p k < m)
    (h2 : m < nth p (k + 1)) : ¬ p m := fun hm => by
  have := nth_succ_le hinf hm h1; omega

end nth

end OpenProblemsLab.FibWalk
