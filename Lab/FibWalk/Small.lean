import Lab.FibWalk.Basic

/-!
# Finite checks for the down- and up-integers

A Boolean description `downB`/`upB` of down- and up-integers that is correct below `377 = f₁₄`,
and the finite facts used in the main proof:
* no window `[N, N+9]` with `N ≤ 104` has `N`, `N + 9` down and exactly three down-integers
  strictly between them (Aliabadi's Lemma 4.1);
* `8, 11, 14, 16, 17` are consecutive up-integers, i.e. the 4th and 8th (`nth` 3 and 7).
-/

namespace OpenProblemsLab.FibWalk

open Nat (fib fib_pos fib_add_two count)

/-- Is there a valid representation of `n` with parameter `t`? (Search over `a ≤ f_t`.) -/
def repAt (n t : ℕ) : Bool :=
  (List.range (fib t + 1)).any fun a =>
    decide (1 ≤ a) && decide (a * fib t ≤ n) &&
      (decide ((n - a * fib t) % fib (t - 1) = 0) && decide (a ≤ (n - a * fib t) / fib (t - 1)) &&
        decide ((n - a * fib t) / fib (t - 1) ≤ fib t))

lemma repAt_iff {n t : ℕ} (ht : 2 ≤ t) : repAt n t = true ↔ ∃ a b, IsRep n t a b := by
  have hf1 : 0 < fib (t - 1) := fib_pos.2 (by omega)
  simp only [repAt, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, -, ⟨ha1, ham⟩, ⟨hmod, hab⟩, hbt⟩
    refine ⟨a, (n - a * fib t) / fib (t - 1), ht, ha1, hab, hbt, ?_⟩
    rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)]
    omega
  · rintro ⟨a, b, -, ha1, hab, hbt, rfl⟩
    have hq : (a * fib t + b * fib (t - 1) - a * fib t) = b * fib (t - 1) := by omega
    refine ⟨a, by omega, ⟨ha1, by omega⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      simp only [hq, Nat.mul_mod_left, Nat.mul_div_cancel _ hf1] <;> omega

/-- Down-integers, checkably (correct below `377`). -/
def downB (n : ℕ) : Bool :=
  (List.range 14).any fun t => decide (2 ≤ t) && decide (t % 2 = 0) && decide (fib t ≤ n) && repAt n t

/-- Up-integers, checkably (correct below `377`). -/
def upB (n : ℕ) : Bool :=
  (List.range 14).any fun t => decide (2 ≤ t) && decide (t % 2 = 1) && decide (fib t ≤ n) && repAt n t

lemma t_lt_14 {n t a b : ℕ} (h : IsRep n t a b) (hn : n < 377) : t < 14 ∧ fib t ≤ n := by
  obtain ⟨-, ha, -, -, rfl⟩ := h
  have h1 : fib t ≤ a * fib t + b * fib (t - 1) := by nlinarith
  refine ⟨?_, h1⟩
  by_contra h14
  have : fib 14 ≤ fib t := Nat.fib_mono (by omega)
  have : fib 14 = 377 := by decide
  omega

lemma isDown_iff_downB {n : ℕ} (hn : n < 377) : IsDown n ↔ downB n = true := by
  simp only [downB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨t, a, b, hr, he⟩
    obtain ⟨h14, hf⟩ := t_lt_14 hr hn
    exact ⟨t, h14, ⟨⟨hr.1, Nat.even_iff.1 he⟩, hf⟩, (repAt_iff hr.1).2 ⟨a, b, hr⟩⟩
  · rintro ⟨t, -, ⟨⟨ht, he⟩, -⟩, hr⟩
    obtain ⟨a, b, hr⟩ := (repAt_iff ht).1 hr
    exact ⟨t, a, b, hr, Nat.even_iff.2 he⟩

lemma isUp_iff_upB {n : ℕ} (hn : n < 377) : IsUp n ↔ upB n = true := by
  simp only [upB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨t, a, b, hr, ho⟩
    obtain ⟨h14, hf⟩ := t_lt_14 hr hn
    exact ⟨t, h14, ⟨⟨hr.1, Nat.odd_iff.1 ho⟩, hf⟩, (repAt_iff hr.1).2 ⟨a, b, hr⟩⟩
  · rintro ⟨t, -, ⟨⟨ht, ho⟩, -⟩, hr⟩
    obtain ⟨a, b, hr⟩ := (repAt_iff ht).1 hr
    exact ⟨t, a, b, hr, Nat.odd_iff.2 ho⟩

/-- The finite window check, in Boolean form. -/
lemma small_windows_B : ∀ N < 105, downB N = true → downB (N + 9) = true →
    count (fun i => downB (N + 1 + i) = true) 8 ≠ 3 := by
  decide

lemma count_congr_lt {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {m : ℕ}
    (h : ∀ i < m, (p i ↔ q i)) : count p m = count q m := by
  simp only [Nat.count_eq_card_filter_range]
  congr 1
  exact Finset.filter_congr fun i hi => h i (Finset.mem_range.1 hi)

/-- **Aliabadi's Lemma 4.1.** No window `[N, N+9]` with `N ≤ 104` has `N`, `N + 9` down and
exactly three down-integers strictly between them. -/
theorem small_windows [DecidablePred IsDown] {N : ℕ} (hN : N ≤ 104) (h0 : IsDown N)
    (h9 : IsDown (N + 9)) : count (fun i => IsDown (N + 1 + i)) 8 ≠ 3 := by
  rw [count_congr_lt (q := fun i => downB (N + 1 + i) = true)
    (fun i hi => isDown_iff_downB (by omega))]
  exact small_windows_B N (by omega) ((isDown_iff_downB (by omega)).1 h0)
    ((isDown_iff_downB (by omega)).1 h9)

/-- `8` and `17` are up-integers, with exactly `3` and `7` up-integers below them. -/
theorem up_facts [DecidablePred IsUp] :
    IsUp 8 ∧ IsUp 17 ∧ count IsUp 8 = 3 ∧ count IsUp 17 = 7 := by
  refine ⟨(isUp_iff_upB (by norm_num)).2 (by decide), (isUp_iff_upB (by norm_num)).2 (by decide),
    ?_, ?_⟩
  · rw [count_congr_lt (q := fun i => upB i = true) (fun i hi => isUp_iff_upB (by omega))]
    decide
  · rw [count_congr_lt (q := fun i => upB i = true) (fun i hi => isUp_iff_upB (by omega))]
    decide

end OpenProblemsLab.FibWalk
