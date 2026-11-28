import Lab.FibWalk.Seven.Patterns

/-!
# `17 ∈ D₇ \ U₇`: the 7-step gap sets differ

Aliabadi (arXiv:2609.04473) and Mao–Zhao (arXiv:2608.19886) show `D₄ ≠ U₄`, and Mao–Zhao show
`D₃ = U₃`. Here we prove `D₇ ≠ U₇`:
* `17 ∈ D₇`: the down-integers `9, 10, 12, 13, 15, 18, 23, 26` are consecutive (`9 + 17 = 26`).
* `17 ∉ U₇`: for `u_k < 105` this is a table check. For `u_k ≥ 105` the seven gaps `s_i` lie in
  `[1, 5]`, and a generated case tree rules out every sequence with sum `17`. Each branch is cut either
  by arithmetic or by a window lemma from `Seven/Patterns.lean`.
-/

namespace OpenProblemsLab.FibWalk

open Nat (count nth)
open scoped Classical

/-- A window from a member `N` to a member `N + g`, with exactly `ℓ - 1` members strictly between,
gives `nth p (count p N + ℓ) = N + g`. -/
lemma nth_add_of_window {p : ℕ → Prop} [DecidablePred p] {N g ℓ : ℕ} (hg : 1 ≤ g) (hℓ : 1 ≤ ℓ)
    (hN : p N) (hM : p (N + g)) (hw : count (fun i => p (N + 1 + i)) (g - 1) = ℓ - 1) :
    nth p (count p N + ℓ) = N + g := by
  have h1 : count p (N + 1) = count p N + 1 := by rw [Nat.count_succ, if_pos hN]
  have h2 : count p (N + g) = count p N + ℓ := by
    have := Nat.count_add p (N + 1) (g - 1)
    rw [show N + 1 + (g - 1) = N + g by omega, h1, hw] at this
    omega
  rw [← h2, Nat.nth_count hM]

lemma dt_wit7 : (dt 9 && dt (9 + 17) && (count (fun i => dt (9 + 1 + i) = true) 16 == 6)) = true := by
  decide +kernel

/-- **`17 ∈ D₇`**. -/
theorem seventeen_mem_down : 17 ∈ gapSet IsDown 7 := by
  have h := dt_wit7
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hN := (isDown_iff_dt (by norm_num)).2 h0
  have hM := (isDown_iff_dt (by norm_num)).2 h1
  have hw : count (fun i => IsDown (9 + 1 + i)) (17 - 1) = 7 - 1 := by
    rw [count_congr_lt (q := fun i => dt (9 + 1 + i) = true)
      (fun i hi => isDown_iff_dt (by omega))]
    exact h2
  refine ⟨count IsDown 9, ?_⟩
  rw [nth_add_of_window (by norm_num) (by norm_num) hN hM hw, Nat.nth_count hN]

lemma ut_small7 : ∀ N < 105, ut N = true →
    ¬ (ut (N + 17) = true ∧ count (fun i => ut (N + 1 + i) = true) 16 = 6) := by
  decide +kernel

/-- **`17 ∉ U₇`**. -/
theorem seventeen_not_mem_up : 17 ∉ gapSet IsUp 7 := by
  rintro ⟨k, hk⟩
  have hinf := up_infinite
  have hmono := Nat.nth_strictMono hinf
  have hT0 : IsUp (nth IsUp k) := Nat.nth_mem_of_infinite hinf k
  have hc0 : count IsUp (nth IsUp k) = k := Nat.count_nth_of_infinite hinf k
  rcases lt_or_ge (nth IsUp k) 105 with hs | hn
  · have h7 : nth IsUp (k + 7) = nth IsUp k + 17 := by
      have := hmono (show k < k + 7 by omega); omega
    have hM : IsUp (nth IsUp k + 17) := h7 ▸ Nat.nth_mem_of_infinite hinf (k + 7)
    have hc7 : count IsUp (nth IsUp k + 17) = k + 7 := h7 ▸ Nat.count_nth_of_infinite hinf (k + 7)
    have hc1 : count IsUp (nth IsUp k + 1) = k + 1 := by rw [Nat.count_succ, hc0, if_pos hT0]
    have hw : count (fun i => IsUp (nth IsUp k + 1 + i)) 16 = 6 := by
      have := Nat.count_add IsUp (nth IsUp k + 1) 16
      rw [show nth IsUp k + 1 + 16 = nth IsUp k + 17 by omega, hc7, hc1] at this
      omega
    rw [count_congr_lt (q := fun i => ut (nth IsUp k + 1 + i) = true)
      (fun i hi => isUp_iff_ut (by omega))] at hw
    exact ut_small7 _ hs ((isUp_iff_ut (by omega)).1 hT0) ⟨(isUp_iff_ut (by omega)).1 hM, hw⟩
  have l1 : nth IsUp k < nth IsUp (k + 1) := hmono (by omega)
  have g1 : nth IsUp (k + 1) ≤ nth IsUp k + 5 := gap_le_five_U k (by omega)
  obtain ⟨s1, E1⟩ : ∃ s, nth IsUp (k + 1) = nth IsUp k + s := ⟨_, (Nat.add_sub_cancel' l1.le).symm⟩
  have s1l : 1 ≤ s1 := by omega
  have s1u : s1 ≤ 5 := by omega
  have l2 : nth IsUp (k + 1) < nth IsUp (k + 2) := hmono (by omega)
  have g2 : nth IsUp (k + 2) ≤ nth IsUp (k + 1) + 5 := gap_le_five_U (k + 1) (by omega)
  obtain ⟨s2, E2⟩ : ∃ s, nth IsUp (k + 2) = nth IsUp (k + 1) + s := ⟨_, (Nat.add_sub_cancel' l2.le).symm⟩
  have s2l : 1 ≤ s2 := by omega
  have s2u : s2 ≤ 5 := by omega
  have l3 : nth IsUp (k + 2) < nth IsUp (k + 3) := hmono (by omega)
  have g3 : nth IsUp (k + 3) ≤ nth IsUp (k + 2) + 5 := gap_le_five_U (k + 2) (by omega)
  obtain ⟨s3, E3⟩ : ∃ s, nth IsUp (k + 3) = nth IsUp (k + 2) + s := ⟨_, (Nat.add_sub_cancel' l3.le).symm⟩
  have s3l : 1 ≤ s3 := by omega
  have s3u : s3 ≤ 5 := by omega
  have l4 : nth IsUp (k + 3) < nth IsUp (k + 4) := hmono (by omega)
  have g4 : nth IsUp (k + 4) ≤ nth IsUp (k + 3) + 5 := gap_le_five_U (k + 3) (by omega)
  obtain ⟨s4, E4⟩ : ∃ s, nth IsUp (k + 4) = nth IsUp (k + 3) + s := ⟨_, (Nat.add_sub_cancel' l4.le).symm⟩
  have s4l : 1 ≤ s4 := by omega
  have s4u : s4 ≤ 5 := by omega
  have l5 : nth IsUp (k + 4) < nth IsUp (k + 5) := hmono (by omega)
  have g5 : nth IsUp (k + 5) ≤ nth IsUp (k + 4) + 5 := gap_le_five_U (k + 4) (by omega)
  obtain ⟨s5, E5⟩ : ∃ s, nth IsUp (k + 5) = nth IsUp (k + 4) + s := ⟨_, (Nat.add_sub_cancel' l5.le).symm⟩
  have s5l : 1 ≤ s5 := by omega
  have s5u : s5 ≤ 5 := by omega
  have l6 : nth IsUp (k + 5) < nth IsUp (k + 6) := hmono (by omega)
  have g6 : nth IsUp (k + 6) ≤ nth IsUp (k + 5) + 5 := gap_le_five_U (k + 5) (by omega)
  obtain ⟨s6, E6⟩ : ∃ s, nth IsUp (k + 6) = nth IsUp (k + 5) + s := ⟨_, (Nat.add_sub_cancel' l6.le).symm⟩
  have s6l : 1 ≤ s6 := by omega
  have s6u : s6 ≤ 5 := by omega
  have l7 : nth IsUp (k + 6) < nth IsUp (k + 7) := hmono (by omega)
  have g7 : nth IsUp (k + 7) ≤ nth IsUp (k + 6) + 5 := gap_le_five_U (k + 6) (by omega)
  obtain ⟨s7, E7⟩ : ∃ s, nth IsUp (k + 7) = nth IsUp (k + 6) + s := ⟨_, (Nat.add_sub_cancel' l7.le).symm⟩
  have s7l : 1 ≤ s7 := by omega
  have s7u : s7 ≤ 5 := by omega
  interval_cases s1
  · interval_cases s2
    · interval_cases s3
      · interval_cases s4
        · exact (w0_1_2_3_4 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
        · interval_cases s5
          · omega
          · exact (w0_1_2_4_6 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) (k4 := k + 5) rfl rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
          · exact (w0_1_2_4_7 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) (k4 := k + 5) rfl rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_2_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_1_4 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_1_6 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
      · interval_cases s4
        · interval_cases s5
          · omega
          · interval_cases s6
            · omega
            · omega
            · omega
            · omega
            · exact (w0_2_7 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_1_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_1_6 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_1_2_4_6 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
        · exact (w0_1_2_4_7 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_2_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
      · exact (w0_1_4 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
      · exact (w0_4 (k0 := k + 2) (k1 := k + 3) rfl (nth IsUp (k + 2)) (by omega) rfl (by omega)).elim
      · exact (w0_1_6 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
    · interval_cases s3
      · interval_cases s4
        · interval_cases s5
          · omega
          · exact (w0_2_3_4_6 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) (k4 := k + 5) rfl rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
          · exact (w0_1_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_1_6 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · interval_cases s5
          · interval_cases s6
            · omega
            · omega
            · omega
            · omega
            · exact (w0_1_6 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · interval_cases s6
            · omega
            · omega
            · omega
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_2_7 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_1_3_4_6_9 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) (k5 := k + 5) rfl rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_2_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_1_4 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_1_6 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
      · interval_cases s4
        · interval_cases s5
          · exact (w0_2_4_5_6 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) (k4 := k + 5) rfl rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
          · interval_cases s6
            · omega
            · omega
            · omega
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_2_7 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_1_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_1_6 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_2_4_6 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega)).elim
        · exact (w0_2_4_7 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega)).elim
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_2_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
      · interval_cases s4
        · exact (w0_3_4 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · interval_cases s5
          · interval_cases s6
            · omega
            · omega
            · exact (w0_1_4 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_1_6 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_3_5_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega)).elim
          · interval_cases s6
            · exact (w0_3_4 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
            · interval_cases s7
              · omega
              · omega
              · omega
              · exact (w0_4 (k0 := k + 6) (k1 := k + 7) rfl (nth IsUp (k + 6)) (by omega) rfl (by omega)).elim
              · omega
            · interval_cases s7
              · omega
              · omega
              · exact (w0_3_6_9 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) (k3 := k + 7) rfl rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega) (by omega)).elim
              · omega
              · omega
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · interval_cases s7
              · exact (w0_5_6 (k0 := k + 5) (k1 := k + 6) (k2 := k + 7) rfl rfl (nth IsUp (k + 5)) (by omega) rfl (by omega) (by omega)).elim
              · omega
              · omega
              · omega
              · omega
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_2_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_1_3_6_9 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_1_3_6_11 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
      · exact (w0_4 (k0 := k + 2) (k1 := k + 3) rfl (nth IsUp (k + 2)) (by omega) rfl (by omega)).elim
      · exact (w0_2_7 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
    · exact (w0_1_4 (k0 := k) (k1 := k + 1) (k2 := k + 2) rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega)).elim
    · exact (w0_4 (k0 := k + 1) (k1 := k + 2) rfl (nth IsUp (k + 1)) (by omega) rfl (by omega)).elim
    · exact (w0_1_6 (k0 := k) (k1 := k + 1) (k2 := k + 2) rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega)).elim
  · interval_cases s2
    · interval_cases s3
      · interval_cases s4
        · interval_cases s5
          · omega
          · interval_cases s6
            · omega
            · omega
            · omega
            · omega
            · exact (w0_2_7 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_1_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_1_6 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_2_3_4_6 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
        · exact (w0_1_4 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_1_6 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
      · interval_cases s4
        · interval_cases s5
          · interval_cases s6
            · omega
            · omega
            · omega
            · omega
            · exact (w0_1_6 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · interval_cases s6
            · omega
            · omega
            · omega
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_2_7 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_1_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_1_6 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · interval_cases s5
          · interval_cases s6
            · omega
            · omega
            · omega
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_1_6 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_2_4_6 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega)).elim
          · exact (w0_2_4_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_2_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · interval_cases s5
          · exact (w0_3_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · interval_cases s6
            · omega
            · exact (w0_3_5_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) (k3 := k + 6) rfl rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega) (by omega)).elim
            · interval_cases s7
              · omega
              · omega
              · omega
              · exact (w0_4 (k0 := k + 6) (k1 := k + 7) rfl (nth IsUp (k + 6)) (by omega) rfl (by omega)).elim
              · omega
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_2_7 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_1_3_6_9 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) (k4 := k + 5) rfl rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_1_3_6_11 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) (k4 := k + 5) rfl rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_2_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
      · exact (w0_1_4 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
      · exact (w0_4 (k0 := k + 2) (k1 := k + 3) rfl (nth IsUp (k + 2)) (by omega) rfl (by omega)).elim
      · exact (w0_1_6 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
    · interval_cases s3
      · interval_cases s4
        · exact (w0_2_4_5_6 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
        · interval_cases s5
          · interval_cases s6
            · omega
            · omega
            · omega
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_1_6 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · interval_cases s6
            · omega
            · omega
            · exact (w0_2_4_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) (k3 := k + 6) rfl rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega) (by omega)).elim
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_2_7 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · interval_cases s6
            · omega
            · interval_cases s7
              · omega
              · omega
              · omega
              · omega
              · exact (w0_2_7 (k0 := k + 5) (k1 := k + 6) (k2 := k + 7) rfl rfl (nth IsUp (k + 5)) (by omega) rfl (by omega) (by omega)).elim
            · exact (w0_1_3_6_9 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) (k4 := k + 6) rfl rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_1_3_6_11 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) (k4 := k + 6) rfl rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_2_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_1_4 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_1_6 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
      · exact (w0_2_4_6 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega)).elim
      · exact (w0_2_4_7 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega)).elim
      · exact (w0_4 (k0 := k + 2) (k1 := k + 3) rfl (nth IsUp (k + 2)) (by omega) rfl (by omega)).elim
      · exact (w0_2_7 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
    · interval_cases s3
      · exact (w0_3_4 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
      · interval_cases s4
        · interval_cases s5
          · exact (w0_3_5_6_7 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) (k4 := k + 5) rfl rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
          · interval_cases s6
            · omega
            · interval_cases s7
              · omega
              · omega
              · omega
              · omega
              · exact (w0_2_7 (k0 := k + 5) (k1 := k + 6) (k2 := k + 7) rfl rfl (nth IsUp (k + 5)) (by omega) rfl (by omega) (by omega)).elim
            · interval_cases s7
              · omega
              · omega
              · omega
              · exact (w0_4 (k0 := k + 6) (k1 := k + 7) rfl (nth IsUp (k + 6)) (by omega) rfl (by omega)).elim
              · omega
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_2_7 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_1_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_1_6 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_3_5_7 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega)).elim
        · interval_cases s5
          · exact (w0_3_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · interval_cases s6
            · interval_cases s7
              · omega
              · omega
              · omega
              · exact (w0_4 (k0 := k + 6) (k1 := k + 7) rfl (nth IsUp (k + 6)) (by omega) rfl (by omega)).elim
              · omega
            · exact (w0_3_5_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) (k3 := k + 6) rfl rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega) (by omega)).elim
            · interval_cases s7
              · omega
              · exact (w0_3_5_8_10_13_15 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) (k4 := k + 5) (k5 := k + 6) (k6 := k + 7) rfl rfl rfl rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).elim
              · omega
              · omega
              · omega
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · omega
          · interval_cases s6
            · exact (w0_3_4 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
            · interval_cases s7
              · omega
              · exact (w0_3_5_7 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) (k3 := k + 7) rfl rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega) (by omega)).elim
              · omega
              · omega
              · omega
            · exact (w0_3_6_9 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) (k3 := k + 6) rfl rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega) (by omega)).elim
            · omega
            · omega
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · interval_cases s6
            · exact (w0_5_6 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
            · omega
            · omega
            · omega
            · omega
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_2_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
      · interval_cases s4
        · exact (w0_3_4 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · interval_cases s5
          · exact (w0_3_6_8_9 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) (k4 := k + 5) rfl rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
          · exact (w0_3_5_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega)).elim
          · interval_cases s6
            · exact (w0_3_4 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
            · interval_cases s7
              · omega
              · exact (w0_3_5_7 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) (k3 := k + 7) rfl rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega) (by omega)).elim
              · omega
              · omega
              · omega
            · interval_cases s7
              · exact (w0_3_4 (k0 := k + 5) (k1 := k + 6) (k2 := k + 7) rfl rfl (nth IsUp (k + 5)) (by omega) rfl (by omega) (by omega)).elim
              · omega
              · omega
              · omega
              · omega
            · omega
            · omega
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_2_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_3_6_9 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega)).elim
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_3_6_11 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega)).elim
      · exact (w0_4 (k0 := k + 2) (k1 := k + 3) rfl (nth IsUp (k + 2)) (by omega) rfl (by omega)).elim
      · interval_cases s4
        · exact (w0_5_6 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_5_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · interval_cases s5
          · exact (w0_3_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · interval_cases s6
            · exact (w0_5_8_10_11 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) (k4 := k + 6) rfl rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
          · omega
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · omega
    · exact (w0_4 (k0 := k + 1) (k1 := k + 2) rfl (nth IsUp (k + 1)) (by omega) rfl (by omega)).elim
    · exact (w0_2_7 (k0 := k) (k1 := k + 1) (k2 := k + 2) rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega)).elim
  · interval_cases s2
    · exact (w0_3_4 (k0 := k) (k1 := k + 1) (k2 := k + 2) rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega)).elim
    · interval_cases s3
      · interval_cases s4
        · exact (w0_3_5_6_7 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
        · interval_cases s5
          · exact (w0_3_5_6_8_9 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) (k5 := k + 5) rfl rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega) (by omega)).elim
          · interval_cases s6
            · omega
            · exact (w0_2_4_6 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) (k3 := k + 6) rfl rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega) (by omega)).elim
            · exact (w0_2_4_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) (k3 := k + 6) rfl rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega) (by omega)).elim
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_2_7 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · interval_cases s6
            · exact (w0_3_4 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
            · interval_cases s7
              · omega
              · omega
              · omega
              · exact (w0_4 (k0 := k + 6) (k1 := k + 7) rfl (nth IsUp (k + 6)) (by omega) rfl (by omega)).elim
              · omega
            · exact (w0_1_3_6_9 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) (k4 := k + 6) rfl rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_1_3_6_11 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) (k4 := k + 6) rfl rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_2_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_1_4 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_1_6 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
      · exact (w0_3_5_7 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega)).elim
      · interval_cases s4
        · exact (w0_3_4 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · interval_cases s5
          · interval_cases s6
            · exact (w0_3_5_6_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) (k4 := k + 6) rfl rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
            · interval_cases s7
              · omega
              · omega
              · omega
              · exact (w0_4 (k0 := k + 6) (k1 := k + 7) rfl (nth IsUp (k + 6)) (by omega) rfl (by omega)).elim
              · omega
            · exact (w0_1_4 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
            · exact (w0_4 (k0 := k + 5) (k1 := k + 6) rfl (nth IsUp (k + 5)) (by omega) rfl (by omega)).elim
            · exact (w0_1_6 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_3_5_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega)).elim
          · interval_cases s6
            · exact (w0_3_4 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
            · exact (w0_3_5_8_10_13_15 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) (k5 := k + 5) (k6 := k + 6) rfl rfl rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).elim
            · interval_cases s7
              · exact (w0_3_4 (k0 := k + 5) (k1 := k + 6) (k2 := k + 7) rfl rfl (nth IsUp (k + 5)) (by omega) rfl (by omega) (by omega)).elim
              · omega
              · omega
              · omega
              · omega
            · omega
            · omega
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · exact (w0_2_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
        · interval_cases s5
          · exact (w0_3_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · interval_cases s6
            · exact (w0_3_6_8_9 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) (k4 := k + 6) rfl rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
            · exact (w0_3_5_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) (k3 := k + 6) rfl rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega) (by omega)).elim
            · interval_cases s7
              · exact (w0_3_4 (k0 := k + 5) (k1 := k + 6) (k2 := k + 7) rfl rfl (nth IsUp (k + 5)) (by omega) rfl (by omega) (by omega)).elim
              · omega
              · omega
              · omega
              · omega
            · omega
            · omega
          · exact (w0_3_6_9 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega)).elim
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · omega
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · interval_cases s5
          · exact (w0_5_6 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_5_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · omega
          · omega
          · omega
      · exact (w0_4 (k0 := k + 2) (k1 := k + 3) rfl (nth IsUp (k + 2)) (by omega) rfl (by omega)).elim
      · exact (w0_2_7 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
    · interval_cases s3
      · exact (w0_3_4 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
      · interval_cases s4
        · exact (w0_3_6_8_9 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
        · exact (w0_3_5_7 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega)).elim
        · interval_cases s5
          · exact (w0_3_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · interval_cases s6
            · interval_cases s7
              · omega
              · omega
              · exact (w0_1_4 (k0 := k + 5) (k1 := k + 6) (k2 := k + 7) rfl rfl (nth IsUp (k + 5)) (by omega) rfl (by omega) (by omega)).elim
              · omega
              · omega
            · exact (w0_3_5_7 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) (k3 := k + 6) rfl rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega) (by omega)).elim
            · interval_cases s7
              · exact (w0_3_4 (k0 := k + 5) (k1 := k + 6) (k2 := k + 7) rfl rfl (nth IsUp (k + 5)) (by omega) rfl (by omega) (by omega)).elim
              · omega
              · omega
              · omega
              · omega
            · omega
            · omega
          · interval_cases s6
            · exact (w0_3_4 (k0 := k + 4) (k1 := k + 5) (k2 := k + 6) rfl rfl (nth IsUp (k + 4)) (by omega) rfl (by omega) (by omega)).elim
            · interval_cases s7
              · exact (w0_3_6_8_9 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) (k3 := k + 6) (k4 := k + 7) rfl rfl rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
              · omega
              · omega
              · omega
              · omega
            · omega
            · omega
            · omega
          · exact (w0_4 (k0 := k + 4) (k1 := k + 5) rfl (nth IsUp (k + 4)) (by omega) rfl (by omega)).elim
          · omega
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · exact (w0_2_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
      · exact (w0_3_6_9 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega)).elim
      · exact (w0_4 (k0 := k + 2) (k1 := k + 3) rfl (nth IsUp (k + 2)) (by omega) rfl (by omega)).elim
      · exact (w0_3_6_11 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega)).elim
    · exact (w0_4 (k0 := k + 1) (k1 := k + 2) rfl (nth IsUp (k + 1)) (by omega) rfl (by omega)).elim
    · interval_cases s3
      · exact (w0_5_6 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
      · exact (w0_5_7 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
      · interval_cases s4
        · exact (w0_3_4 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · interval_cases s5
          · exact (w0_5_8_10_11 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) (k4 := k + 5) rfl rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
          · exact (w0_3_5_7 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) (k3 := k + 5) rfl rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega) (by omega)).elim
          · omega
          · omega
          · omega
        · exact (w0_5_8_11 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega)).elim
        · omega
        · omega
      · exact (w0_4 (k0 := k + 2) (k1 := k + 3) rfl (nth IsUp (k + 2)) (by omega) rfl (by omega)).elim
      · interval_cases s4
        · exact (w0_5_6 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · omega
        · omega
        · omega
        · omega
  · exact (w0_4 (k0 := k) (k1 := k + 1) rfl (nth IsUp (k)) (by omega) rfl (by omega)).elim
  · interval_cases s2
    · exact (w0_5_6 (k0 := k) (k1 := k + 1) (k2 := k + 2) rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega)).elim
    · exact (w0_5_7 (k0 := k) (k1 := k + 1) (k2 := k + 2) rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega)).elim
    · interval_cases s3
      · exact (w0_3_4 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
      · interval_cases s4
        · exact (w0_5_8_10_11 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega)).elim
        · exact (w0_3_5_7 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) (k3 := k + 4) rfl rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega) (by omega)).elim
        · interval_cases s5
          · exact (w0_3_4 (k0 := k + 3) (k1 := k + 4) (k2 := k + 5) rfl rfl (nth IsUp (k + 3)) (by omega) rfl (by omega) (by omega)).elim
          · exact (w0_5_8_10_13_15 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) (k4 := k + 4) (k5 := k + 5) rfl rfl rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega) (by omega) (by omega)).elim
          · omega
          · omega
          · omega
        · exact (w0_4 (k0 := k + 3) (k1 := k + 4) rfl (nth IsUp (k + 3)) (by omega) rfl (by omega)).elim
        · omega
      · exact (w0_5_8_11 (k0 := k) (k1 := k + 1) (k2 := k + 2) (k3 := k + 3) rfl rfl rfl (nth IsUp (k)) (by omega) rfl (by omega) (by omega) (by omega)).elim
      · exact (w0_4 (k0 := k + 2) (k1 := k + 3) rfl (nth IsUp (k + 2)) (by omega) rfl (by omega)).elim
      · interval_cases s4
        · exact (w0_5_6 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · omega
        · omega
        · omega
        · omega
    · exact (w0_4 (k0 := k + 1) (k1 := k + 2) rfl (nth IsUp (k + 1)) (by omega) rfl (by omega)).elim
    · interval_cases s3
      · exact (w0_5_6 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
      · exact (w0_5_7 (k0 := k + 1) (k1 := k + 2) (k2 := k + 3) rfl rfl (nth IsUp (k + 1)) (by omega) rfl (by omega) (by omega)).elim
      · interval_cases s4
        · exact (w0_3_4 (k0 := k + 2) (k1 := k + 3) (k2 := k + 4) rfl rfl (nth IsUp (k + 2)) (by omega) rfl (by omega) (by omega)).elim
        · omega
        · omega
        · omega
        · omega
      · omega
      · omega

/-- **The 7-step gap sets of down- and up-integers differ**: `17 ∈ D₇ \ U₇`. -/
theorem gapSet_seven_ne : gapSet IsDown 7 ≠ gapSet IsUp 7 := fun h =>
  seventeen_not_mem_up (h ▸ seventeen_mem_down)

end OpenProblemsLab.FibWalk
