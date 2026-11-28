import Lab.FibWalk.Three.PatternsD
import Lab.FibWalk.Three.PatternsU
import Lab.FibWalk.Three.Table

/-!
# `D₃ = U₃ = {3, 4, 5, 6, 7, 8, 10, 11, 13}`

Chung, Graham and Spiro asked whether the `ℓ`-step gap sets of down- and up-integers agree.
Aliabadi (arXiv:2609.04473) showed they differ at `ℓ = 4` (formalized in `Main.lean`). Mao and
Zhao (arXiv:2608.19886, Theorem 1.2) proved `D₃ = U₃ = {3,4,5,6,7,8,10,11,13}`. This file proves
that theorem in Lean, with our own argument.

* For a member `n ≥ 105`, the three gaps `a, b, c` to the next three members are each at most `5`
  (`gap_le_five_*`, pattern `gap6`). Every triple with `a + b + c ∈ {9,12,14,15}` is ruled out by a
  window case analysis (`Three/Patterns*.lean`). That analysis uses the threshold lemma and the shift
  lemmas for the same type (down-shifts for `D`, the up-shifts of `Three/Shifts.lean` for `U`).
* Members `n < 105` are handled by explicit tables (`Three/Table.lean`).
* The reverse inclusions come from explicit witnesses.

No uniqueness of the Chung–Graham–Spiro representation is used.
-/

namespace OpenProblemsLab.FibWalk

open Nat (count nth)
open scoped Classical

/-- The common 3-step gap set. -/
def S3 : Set ℕ := {3, 4, 5, 6, 7, 8, 10, 11, 13}

/-- A window `[N, N+g]` from a member `N` to a member `N + g` with exactly two members strictly
between them gives `nth p (count p N + 3) = N + g`. -/
lemma nth_add_three_of_window {p : ℕ → Prop} [DecidablePred p] (hinf : (Set.ofPred p).Infinite)
    {N g : ℕ} (hg : 1 ≤ g) (hN : p N) (hM : p (N + g))
    (hw : count (fun i => p (N + 1 + i)) (g - 1) = 2) : nth p (count p N + 3) = N + g := by
  have h1 : count p (N + 1) = count p N + 1 := by rw [Nat.count_succ, if_pos hN]
  have h2 : count p (N + g) = count p N + 3 := by
    have := Nat.count_add p (N + 1) (g - 1)
    rw [show N + 1 + (g - 1) = N + g by omega, h1, hw] at this
    omega
  rw [← h2, Nat.nth_count hM]

/-- `not_mem_between` with the successor index given separately. -/
lemma not_mem_between' {p : ℕ → Prop} [DecidablePred p] (hinf : (Set.ofPred p).Infinite)
    {k k' m : ℕ} (hk : k' = k + 1) (h1 : nth p k < m) (h2 : m < nth p k') : ¬ p m := by
  subst hk; exact not_mem_between hinf h1 h2

/-- Transfer the Boolean small-window check to `p`. -/
lemma small_of_bool {p : ℕ → Prop} [DecidablePred p] (tb : ℕ → Bool)
    (hp : ∀ m < 310, (p m ↔ tb m = true))
    (hB : ∀ N < 105, tb N = true →
      (S3l.any fun g => tb (N + g) && (count (fun i => tb (N + 1 + i) = true) (g - 1) == 2)) = true)
    {N : ℕ} (hN : N < 105) (hpN : p N) :
    ∃ g ∈ S3, 1 ≤ g ∧ p (N + g) ∧ count (fun i => p (N + 1 + i)) (g - 1) = 2 := by
  have := hB N hN ((hp N (by omega)).1 hpN)
  rw [List.any_eq_true] at this
  obtain ⟨g, hg, h⟩ := this
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hg' : g ∈ S3 ∧ 1 ≤ g ∧ g ≤ 13 := by
    simp only [S3l, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [S3]
  refine ⟨g, hg'.1, hg'.2.1, (hp _ (by omega)).2 h.1, ?_⟩
  rw [count_congr_lt (q := fun i => tb (N + 1 + i) = true) (fun i hi => hp _ (by omega))]
  exact h.2

/-- Transfer a Boolean witness to a gap of `p`. -/
lemma witness_of_bool {p : ℕ → Prop} [DecidablePred p] (hinf : (Set.ofPred p).Infinite)
    (tb : ℕ → Bool) (hp : ∀ m < 310, (p m ↔ tb m = true)) {N g : ℕ} (hg : 1 ≤ g) (hNg : N + g < 310)
    (h : (tb N && tb (N + g) && (count (fun i => tb (N + 1 + i) = true) (g - 1) == 2)) = true) :
    g ∈ gapSet p 3 := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hN := (hp N (by omega)).2 h0
  have hM := (hp (N + g) hNg).2 h1
  have hw : count (fun i => p (N + 1 + i)) (g - 1) = 2 := by
    rw [count_congr_lt (q := fun i => tb (N + 1 + i) = true) (fun i hi => hp _ (by omega))]
    exact h2
  refine ⟨count p N, ?_⟩
  rw [nth_add_three_of_window hinf hg hN hM hw, Nat.nth_count hN]
  omega

/-- Consecutive down-integers `≥ 105` are at most `5` apart. -/
lemma gap_le_five_D (k : ℕ) (hn : 105 ≤ nth IsDown k) : nth IsDown (k + 1) ≤ nth IsDown k + 5 := by
  by_contra hlt
  push Not at hlt
  have hinf := down_infinite
  apply pat_D_gap6 (nth IsDown k) hn
  intro j hj
  constructor
  · intro hT
    by_contra hj0
    exact not_mem_between hinf (k := k) (by omega) (by omega) hT
  · rintro rfl
    simpa using Nat.nth_mem_of_infinite hinf k

/-- Every 3-step gap of the down-integers lies in `S₃`. -/
theorem gap3_down_subset : gapSet IsDown 3 ⊆ S3 := by
  rintro g ⟨k, rfl⟩
  have hinf := down_infinite
  have hmono := Nat.nth_strictMono hinf
  have hT0 : IsDown (nth IsDown k) := Nat.nth_mem_of_infinite hinf k
  have hc0 : count IsDown (nth IsDown k) = k := Nat.count_nth_of_infinite hinf k
  rcases lt_or_ge (nth IsDown k) 105 with hs | hn
  · obtain ⟨g, hgS, hg1, hTg, hw⟩ := small_of_bool dt (fun m hm => isDown_iff_dt hm)
      dt_small hs hT0
    have := nth_add_three_of_window hinf hg1 hT0 hTg hw
    rw [hc0] at this
    rw [this, show nth IsDown k + g - nth IsDown k = g by omega]
    exact hgS
  have l1 : nth IsDown k < nth IsDown (k + 1) := hmono (by omega)
  have l2 : nth IsDown (k + 1) < nth IsDown (k + 2) := hmono (by omega)
  have l3 : nth IsDown (k + 2) < nth IsDown (k + 3) := hmono (by omega)
  have g1 : nth IsDown (k + 1) ≤ nth IsDown k + 5 := gap_le_five_D k hn
  have g2 : nth IsDown (k + 2) ≤ nth IsDown (k + 1) + 5 := gap_le_five_D (k + 1) (by omega)
  have g3 : nth IsDown (k + 3) ≤ nth IsDown (k + 2) + 5 := gap_le_five_D (k + 2) (by omega)
  have T1 : IsDown (nth IsDown (k + 1)) := Nat.nth_mem_of_infinite hinf _
  have T2 : IsDown (nth IsDown (k + 2)) := Nat.nth_mem_of_infinite hinf _
  have T3 : IsDown (nth IsDown (k + 3)) := Nat.nth_mem_of_infinite hinf _
  set n := nth IsDown k with hn_def
  obtain ⟨a, ha⟩ : ∃ a, nth IsDown (k + 1) = n + a := ⟨_, (Nat.add_sub_cancel' l1.le).symm⟩
  obtain ⟨b, hb⟩ : ∃ b, nth IsDown (k + 2) = n + a + b := ⟨nth IsDown (k + 2) - (n + a), by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, nth IsDown (k + 3) = n + a + b + c := ⟨nth IsDown (k + 3) - (n + a + b), by omega⟩
  have hD : ∀ j ≤ a + b + c, (IsDown (n + j) ↔ j = 0 ∨ j = a ∨ j = a + b ∨ j = a + b + c) := by
    intro j hj
    constructor
    · intro hT
      by_contra hne
      push Not at hne
      rcases (by omega : j < a ∨ (a < j ∧ j < a + b) ∨ (a + b < j ∧ j < a + b + c)) with h | h | h
      · exact not_mem_between' hinf (k := k) (k' := k + 1) rfl (by omega) (by omega) hT
      · exact not_mem_between' hinf (k := k + 1) (k' := k + 2) rfl (by omega) (by omega) hT
      · exact not_mem_between' hinf (k := k + 2) (k' := k + 3) rfl (by omega) (by omega) hT
    · rintro (rfl | rfl | rfl | rfl)
      · simpa using hT0
      · simpa [ha] using T1
      · simpa [hb, add_assoc] using T2
      · simpa [hc, add_assoc] using T3
  rw [hc, show n + a + b + c - n = a + b + c by omega]
  have ha1 : 1 ≤ a := by omega
  have ha5 : a ≤ 5 := by omega
  have hb1 : 1 ≤ b := by omega
  have hb5 : b ≤ 5 := by omega
  have hc1 : 1 ≤ c := by omega
  have hc5 : c ≤ 5 := by omega
  clear_value n
  interval_cases a <;> interval_cases b <;> interval_cases c
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_1_3_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_1_4_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_1_5_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_2_2_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_2_3_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_2_4_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_2_5_2 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_D_2_5_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_3_1_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_3_2_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_3_3_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_3_4_2 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_D_3_4_5 n hn (by simpa using hD)).elim
  · exact (pat_D_3_5_1 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_D_3_5_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_4_1_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_4_2_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_4_3_2 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_D_4_3_5 n hn (by simpa using hD)).elim
  · exact (pat_D_4_4_1 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_D_4_4_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_4_5_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · exact (pat_D_4_5_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_D_5_1_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_5_2_2 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_D_5_2_5 n hn (by simpa using hD)).elim
  · exact (pat_D_5_3_1 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_D_5_3_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_D_5_4_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · exact (pat_D_5_4_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · exact (pat_D_5_5_2 n hn (by simpa using hD)).elim
  · simp [S3]
  · exact (pat_D_5_5_4 n hn (by simpa using hD)).elim
  · exact (pat_D_5_5_5 n hn (by simpa using hD)).elim

/-- Every `g ∈ S₃` is a 3-step gap of the down-integers. -/
theorem S3_subset_gap3_down : S3 ⊆ gapSet IsDown 3 := by
  intro g hg
  simp only [S3, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  have h := fun m (hm : m < 310) => isDown_iff_dt hm
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_of_bool down_infinite dt h (N := 46) (by norm_num) (by norm_num) dt_wit_3
  · exact witness_of_bool down_infinite dt h (N := 9) (by norm_num) (by norm_num) dt_wit_4
  · exact witness_of_bool down_infinite dt h (N := 5) (by norm_num) (by norm_num) dt_wit_5
  · exact witness_of_bool down_infinite dt h (N := 12) (by norm_num) (by norm_num) dt_wit_6
  · exact witness_of_bool down_infinite dt h (N := 2) (by norm_num) (by norm_num) dt_wit_7
  · exact witness_of_bool down_infinite dt h (N := 23) (by norm_num) (by norm_num) dt_wit_8
  · exact witness_of_bool down_infinite dt h (N := 13) (by norm_num) (by norm_num) dt_wit_10
  · exact witness_of_bool down_infinite dt h (N := 15) (by norm_num) (by norm_num) dt_wit_11
  · exact witness_of_bool down_infinite dt h (N := 107) (by norm_num) (by norm_num) dt_wit_13

/-- Consecutive up-integers `≥ 105` are at most `5` apart. -/
lemma gap_le_five_U (k : ℕ) (hn : 105 ≤ nth IsUp k) : nth IsUp (k + 1) ≤ nth IsUp k + 5 := by
  by_contra hlt
  push Not at hlt
  have hinf := up_infinite
  apply pat_U_gap6 (nth IsUp k) hn
  intro j hj
  constructor
  · intro hT
    by_contra hj0
    exact not_mem_between hinf (k := k) (by omega) (by omega) hT
  · rintro rfl
    simpa using Nat.nth_mem_of_infinite hinf k

/-- Every 3-step gap of the up-integers lies in `S₃`. -/
theorem gap3_up_subset : gapSet IsUp 3 ⊆ S3 := by
  rintro g ⟨k, rfl⟩
  have hinf := up_infinite
  have hmono := Nat.nth_strictMono hinf
  have hT0 : IsUp (nth IsUp k) := Nat.nth_mem_of_infinite hinf k
  have hc0 : count IsUp (nth IsUp k) = k := Nat.count_nth_of_infinite hinf k
  rcases lt_or_ge (nth IsUp k) 105 with hs | hn
  · obtain ⟨g, hgS, hg1, hTg, hw⟩ := small_of_bool ut (fun m hm => isUp_iff_ut hm)
      ut_small hs hT0
    have := nth_add_three_of_window hinf hg1 hT0 hTg hw
    rw [hc0] at this
    rw [this, show nth IsUp k + g - nth IsUp k = g by omega]
    exact hgS
  have l1 : nth IsUp k < nth IsUp (k + 1) := hmono (by omega)
  have l2 : nth IsUp (k + 1) < nth IsUp (k + 2) := hmono (by omega)
  have l3 : nth IsUp (k + 2) < nth IsUp (k + 3) := hmono (by omega)
  have g1 : nth IsUp (k + 1) ≤ nth IsUp k + 5 := gap_le_five_U k hn
  have g2 : nth IsUp (k + 2) ≤ nth IsUp (k + 1) + 5 := gap_le_five_U (k + 1) (by omega)
  have g3 : nth IsUp (k + 3) ≤ nth IsUp (k + 2) + 5 := gap_le_five_U (k + 2) (by omega)
  have T1 : IsUp (nth IsUp (k + 1)) := Nat.nth_mem_of_infinite hinf _
  have T2 : IsUp (nth IsUp (k + 2)) := Nat.nth_mem_of_infinite hinf _
  have T3 : IsUp (nth IsUp (k + 3)) := Nat.nth_mem_of_infinite hinf _
  set n := nth IsUp k with hn_def
  obtain ⟨a, ha⟩ : ∃ a, nth IsUp (k + 1) = n + a := ⟨_, (Nat.add_sub_cancel' l1.le).symm⟩
  obtain ⟨b, hb⟩ : ∃ b, nth IsUp (k + 2) = n + a + b := ⟨nth IsUp (k + 2) - (n + a), by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, nth IsUp (k + 3) = n + a + b + c := ⟨nth IsUp (k + 3) - (n + a + b), by omega⟩
  have hD : ∀ j ≤ a + b + c, (IsUp (n + j) ↔ j = 0 ∨ j = a ∨ j = a + b ∨ j = a + b + c) := by
    intro j hj
    constructor
    · intro hT
      by_contra hne
      push Not at hne
      rcases (by omega : j < a ∨ (a < j ∧ j < a + b) ∨ (a + b < j ∧ j < a + b + c)) with h | h | h
      · exact not_mem_between' hinf (k := k) (k' := k + 1) rfl (by omega) (by omega) hT
      · exact not_mem_between' hinf (k := k + 1) (k' := k + 2) rfl (by omega) (by omega) hT
      · exact not_mem_between' hinf (k := k + 2) (k' := k + 3) rfl (by omega) (by omega) hT
    · rintro (rfl | rfl | rfl | rfl)
      · simpa using hT0
      · simpa [ha] using T1
      · simpa [hb, add_assoc] using T2
      · simpa [hc, add_assoc] using T3
  rw [hc, show n + a + b + c - n = a + b + c by omega]
  have ha1 : 1 ≤ a := by omega
  have ha5 : a ≤ 5 := by omega
  have hb1 : 1 ≤ b := by omega
  have hb5 : b ≤ 5 := by omega
  have hc1 : 1 ≤ c := by omega
  have hc5 : c ≤ 5 := by omega
  clear_value n
  interval_cases a <;> interval_cases b <;> interval_cases c
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_1_3_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_1_4_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_1_5_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_2_2_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_2_3_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_2_4_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_2_5_2 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_U_2_5_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_3_1_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_3_2_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_3_3_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_3_4_2 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_U_3_4_5 n hn (by simpa using hD)).elim
  · exact (pat_U_3_5_1 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_U_3_5_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_4_1_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_4_2_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_4_3_2 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_U_4_3_5 n hn (by simpa using hD)).elim
  · exact (pat_U_4_4_1 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_U_4_4_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_4_5_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · exact (pat_U_4_5_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_U_5_1_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_5_2_2 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_U_5_2_5 n hn (by simpa using hD)).elim
  · exact (pat_U_5_3_1 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · exact (pat_U_5_3_4 n hn (by simpa using hD)).elim
  · simp [S3]
  · simp [S3]
  · simp [S3]
  · exact (pat_U_5_4_3 n hn (by simpa using hD)).elim
  · simp [S3]
  · exact (pat_U_5_4_5 n hn (by simpa using hD)).elim
  · simp [S3]
  · exact (pat_U_5_5_2 n hn (by simpa using hD)).elim
  · simp [S3]
  · exact (pat_U_5_5_4 n hn (by simpa using hD)).elim
  · exact (pat_U_5_5_5 n hn (by simpa using hD)).elim

/-- Every `g ∈ S₃` is a 3-step gap of the up-integers. -/
theorem S3_subset_gap3_up : S3 ⊆ gapSet IsUp 3 := by
  intro g hg
  simp only [S3, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  have h := fun m (hm : m < 310) => isUp_iff_ut hm
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_of_bool up_infinite ut h (N := 19) (by norm_num) (by norm_num) ut_wit_3
  · exact witness_of_bool up_infinite ut h (N := 16) (by norm_num) (by norm_num) ut_wit_4
  · exact witness_of_bool up_infinite ut h (N := 3) (by norm_num) (by norm_num) ut_wit_5
  · exact witness_of_bool up_infinite ut h (N := 11) (by norm_num) (by norm_num) ut_wit_6
  · exact witness_of_bool up_infinite ut h (N := 4) (by norm_num) (by norm_num) ut_wit_7
  · exact witness_of_bool up_infinite ut h (N := 6) (by norm_num) (by norm_num) ut_wit_8
  · exact witness_of_bool up_infinite ut h (N := 40) (by norm_num) (by norm_num) ut_wit_10
  · exact witness_of_bool up_infinite ut h (N := 42) (by norm_num) (by norm_num) ut_wit_11
  · exact witness_of_bool up_infinite ut h (N := 291) (by norm_num) (by norm_num) ut_wit_13

/-- **Mao–Zhao, Theorem 1.2 (`ℓ = 3`)**: `D₃ = U₃ = {3, 4, 5, 6, 7, 8, 10, 11, 13}`. -/
theorem gapSet_three : gapSet IsDown 3 = S3 ∧ gapSet IsUp 3 = S3 :=
  ⟨Set.Subset.antisymm gap3_down_subset S3_subset_gap3_down,
    Set.Subset.antisymm gap3_up_subset S3_subset_gap3_up⟩

/-- The Chung–Graham–Spiro question has a positive answer at `ℓ = 3`: `D₃ = U₃`. -/
theorem down_gapSet_three_eq_up : gapSet IsDown 3 = gapSet IsUp 3 := by
  rw [gapSet_three.1, gapSet_three.2]

end OpenProblemsLab.FibWalk
