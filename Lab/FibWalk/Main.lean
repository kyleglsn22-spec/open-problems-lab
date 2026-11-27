import Lab.FibWalk.Core
import Lab.FibWalk.Small

/-!
# The Chung–Graham–Spiro gap-set conjecture is false: `9 ∈ U₄ \ D₄`

Let `d₀ < d₁ < ⋯` be the down-integers and `u₀ < u₁ < ⋯` the up-integers, and let
`D_ℓ = {d_{k+ℓ} - d_k}` and `U_ℓ = {u_{k+ℓ} - u_k}` be their `ℓ`-step gap sets. Chung, Graham and
Spiro proved `D₁ = U₁` and `D₂ = U₂` and conjectured `D_ℓ = U_ℓ` for every `ℓ ≥ 1`. Aliabadi
(arXiv:2609.04473, Sept 2026) disproved this with `9 ∈ U₄ \ D₄`.

* `nine_mem_up`: `8, 11, 14, 16, 17` are consecutive up-integers, so `9 ∈ U₄`.
* `nine_not_mem_down`: no five consecutive down-integers span exactly `9`.
* `not_gapSet_conjecture`: the conjecture fails at `ℓ = 4`.

Our proof follows Aliabadi's strategy, but is self-contained: it does not use the cited results of
Chung–Graham–Spiro (`D₁ = U₁ = {1,2,3,5}`, `D₂ = U₂`, their Proposition 4.2 and Lemma 4.1). In
their place we prove the threshold lemma and a general shift lemma (`Basic.lean`) and use five
shifts (`+1, -2, +3, -5, +8`) instead of two in the final case analysis (`Core.lean`).
-/

namespace OpenProblemsLab.FibWalk

open Nat (fib fib_pos fib_add_two count nth le_fib_add_one)
open Real
open scoped goldenRatio Classical

lemma isRep_fib {t : ℕ} (ht : 2 ≤ t) : IsRep (fib (t + 1)) t 1 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  refine ⟨ht, le_rfl, le_rfl, fib_pos.2 (by omega), ?_⟩
  rw [show s + 2 + 1 = (s + 1) + 2 from rfl, fib_add_two, show s + 2 - 1 = s + 1 by omega]
  simp only [one_mul]
  rw [add_comm]

lemma down_infinite : (Set.ofPred IsDown).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro m
  refine ⟨fib (2 * m + 2 + 1), ⟨2 * m + 2, 1, 1, isRep_fib (by omega), ⟨m + 1, by omega⟩⟩, ?_⟩
  have := le_fib_add_one (2 * m + 2 + 1)
  omega

lemma up_infinite : (Set.ofPred IsUp).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro m
  refine ⟨fib (2 * m + 3 + 1), ⟨2 * m + 3, 1, 1, isRep_fib (by omega), ⟨m + 1, by omega⟩⟩, ?_⟩
  have := le_fib_add_one (2 * m + 3 + 1)
  omega

/-- Down-integers `≥ 105` have representation parameter `t ≥ 8`. -/
lemma eight_le_of_rep {N t a b : ℕ} (h : IsRep N t a b) (he : Even t) (hN : 105 ≤ N) : 8 ≤ t := by
  by_contra h8
  obtain ⟨ht, -, hab, hbt, rfl⟩ := h
  have hb : a * fib t + b * fib (t - 1) ≤ fib t * fib t + fib t * fib (t - 1) := by
    have : a ≤ fib t := by omega
    exact Nat.add_le_add (Nat.mul_le_mul_right _ this) (Nat.mul_le_mul_right _ hbt)
  have : t = 2 ∨ t = 4 ∨ t = 6 := by
    obtain ⟨k, hk⟩ := he; omega
  rcases this with rfl | rfl | rfl <;>
    simp only [show fib 2 = 1 from rfl, show fib 4 = 3 from rfl, show fib 6 = 8 from rfl,
      show fib (2 - 1) = 1 from rfl, show fib (4 - 1) = 2 from rfl, show fib (6 - 1) = 5 from rfl] at hb hN <;>
    omega

/-- The shift lemma for a down-integer `N ≥ 105`, with the sign written as `(-1)^j`. -/
lemma shift' {N j : ℕ} (θ : ℝ) (hj : 2 ≤ j) (hj7 : j ≤ 7)
    (hθ : θ * √5 * φ ^ (j - 1) = φ ^ (j - 2) + 1) (hN : 105 ≤ N) (h : IsDown N) (hδ : θ ≤ δ N) :
    ∃ n' : ℕ, (n' : ℤ) = N + (-1) ^ j * fib j ∧ IsDown n' := by
  obtain ⟨t, a, b, hr, he⟩ := h
  have ht := eight_le_of_rep hr he hN
  obtain ⟨n', hn', hd⟩ := shift θ hj hθ hr he (by omega) hδ
  refine ⟨n', ?_, hd⟩
  rw [hn']
  congr 2
  rcases Nat.even_or_odd j with hje | hjo
  · rw [hje.neg_one_pow, (Nat.even_sub (by omega)).2 (iff_of_true he hje) |>.neg_one_pow]
  · have : Odd (t - j) := by
      rcases he with ⟨k, hk⟩; rcases hjo with ⟨i, hi⟩; exact ⟨k - i - 1, by omega⟩
    rw [hjo.neg_one_pow, this.neg_one_pow]

lemma shift_plus1 {N : ℕ} (hN : 105 ≤ N) (h : IsDown N) (hδ : θ₂ ≤ δ N) : IsDown (N + 1) := by
  obtain ⟨n', hn', hd⟩ := shift' θ₂ le_rfl (by norm_num) hθ₂ hN h hδ
  have : n' = N + 1 := by norm_num [Nat.fib] at hn'; omega
  rwa [this] at hd

lemma shift_minus2 {N : ℕ} (hN : 105 ≤ N) (h : IsDown N) (hδ : θ₃ ≤ δ N) : IsDown (N - 2) := by
  obtain ⟨n', hn', hd⟩ := shift' θ₃ (by norm_num) (by norm_num) hθ₃ hN h hδ
  have : n' = N - 2 := by norm_num [Nat.fib] at hn'; omega
  rwa [this] at hd

lemma shift_plus3 {N : ℕ} (hN : 105 ≤ N) (h : IsDown N) (hδ : θ₄ ≤ δ N) : IsDown (N + 3) := by
  obtain ⟨n', hn', hd⟩ := shift' θ₄ (by norm_num) (by norm_num) hθ₄ hN h hδ
  have : n' = N + 3 := by norm_num [Nat.fib] at hn'; omega
  rwa [this] at hd

lemma shift_minus5 {N : ℕ} (hN : 105 ≤ N) (h : IsDown N) (hδ : θ₅ ≤ δ N) : IsDown (N - 5) := by
  obtain ⟨n', hn', hd⟩ := shift' θ₅ (by norm_num) (by norm_num) hθ₅ hN h hδ
  have : n' = N - 5 := by norm_num [Nat.fib] at hn'; omega
  rwa [this] at hd

lemma shift_plus8 {N : ℕ} (hN : 105 ≤ N) (h : IsDown N) (hδ : θ₆ ≤ δ N) : IsDown (N + 8) := by
  obtain ⟨n', hn', hd⟩ := shift' θ₆ (by norm_num) (by norm_num) hθ₆ hN h hδ
  have : n' = N + 8 := by norm_num [Nat.fib] at hn'; omega
  rwa [this] at hd

/-- `δ (n + j) = {δ n + {jφ}}`, written with `{jφ} = jφ - f` for `f = ⌊jφ⌋`. -/
lemma delta_add (n j : ℕ) (f : ℤ) (hf0 : (f : ℝ) ≤ j * φ) (hf1 : j * φ < f + 1) :
    δ (n + j) = δ n + (j * φ - f) ∨ δ (n + j) = δ n + (j * φ - f) - 1 := by
  have hfr : Int.fract ((j : ℝ) * φ) = j * φ - f := by
    rw [Int.fract_eq_iff]; exact ⟨by linarith, by linarith, f, by ring⟩
  obtain ⟨z, hz⟩ := Int.fract_add (φ * n) (j * φ)
  have e : δ (n + j) = Int.fract (φ * n + j * φ) := by rw [δ]; push_cast; ring_nf
  have h1 := Int.fract_nonneg (φ * n + j * φ)
  have h2 := Int.fract_lt_one (φ * n + j * φ)
  have h3 := Int.fract_nonneg (φ * n)
  have h4 := Int.fract_lt_one (φ * n)
  rw [hfr] at hz
  have hz1 : (z : ℝ) < 1 := by linarith
  have hz2 : (-2 : ℝ) < z := by linarith
  have : z = 0 ∨ z = -1 := by
    have : z < 1 := by exact_mod_cast hz1
    have : -2 < z := by exact_mod_cast hz2
    omega
  rw [e, δ]
  rcases this with rfl | rfl
  · left; push_cast at hz; linarith
  · right; push_cast at hz; linarith

/-- **`9 ∉ D₄`**: no five consecutive down-integers span exactly `9`. -/
theorem nine_not_mem_down : 9 ∉ gapSet IsDown 4 := by
  rintro ⟨k, hk⟩
  have hinf := down_infinite
  have hmono := Nat.nth_strictMono hinf
  set n := nth IsDown k with hn
  have h4 : nth IsDown (k + 4) = n + 9 := by
    have := hmono (show k < k + 4 by omega); omega
  have hDn : IsDown n := Nat.nth_mem_of_infinite hinf k
  have hD9 : IsDown (n + 9) := h4 ▸ Nat.nth_mem_of_infinite hinf (k + 4)
  have hc0 : count IsDown n = k := Nat.count_nth_of_infinite hinf k
  have hc9 : count IsDown (n + 9) = k + 4 := by
    rw [← h4]; exact Nat.count_nth_of_infinite hinf _
  have hc1 : count IsDown (n + 1) = k + 1 := by rw [Nat.count_succ, hc0, if_pos hDn]
  have hc : count (fun i => IsDown (n + 1 + i)) 8 = 3 := by
    have := Nat.count_add IsDown (n + 1) 8
    rw [show n + 1 + 8 = n + 9 by omega, hc9, hc1] at this
    omega
  rcases le_or_gt n 104 with hsmall | hbig
  · exact small_windows hsmall hDn hD9 hc
  have hp := phi_bounds
  have U : ∀ j, ¬ IsDown (n + j) → η < δ (n + j) := fun j h =>
    (isUp_of_not_isDown (by omega) h).lt_delta
  have P1 := fun p (hp : IsDown (n + p)) (hq : ¬ IsDown (n + p + 1)) =>
    lt_of_not_ge fun hθ => hq (shift_plus1 (by omega) hp hθ)
  have M2 := fun p (hp2 : 2 ≤ p) (hp : IsDown (n + p)) (hq : ¬ IsDown (n + (p - 2))) =>
    lt_of_not_ge fun hθ => hq (by
      have := shift_minus2 (by omega) hp hθ; rwa [show n + p - 2 = n + (p - 2) by omega] at this)
  have P3 := fun p (hp : IsDown (n + p)) (hq : ¬ IsDown (n + p + 3)) =>
    lt_of_not_ge fun hθ => hq (shift_plus3 (by omega) hp hθ)
  have M5 := fun p (hp5 : 5 ≤ p) (hp : IsDown (n + p)) (hq : ¬ IsDown (n + (p - 5))) =>
    lt_of_not_ge fun hθ => hq (by
      have := shift_minus5 (by omega) hp hθ; rwa [show n + p - 5 = n + (p - 5) by omega] at this)
  have P8 := fun p (hp : IsDown (n + p)) (hq : ¬ IsDown (n + p + 8)) =>
    lt_of_not_ge fun hθ => hq (shift_plus8 (by omega) hp hθ)
  have hDn' : IsDown (n + 0) := hDn
  have hD9' : IsDown (n + 9) := hD9
  refine core (δ n) (δ (n + 1)) (δ (n + 2)) (δ (n + 3)) (δ (n + 4)) (δ (n + 5)) (δ (n + 6))
    (δ (n + 7)) (δ (n + 8)) (δ (n + 9)) (IsDown (n + 1)) (IsDown (n + 2)) (IsDown (n + 3))
    (IsDown (n + 4)) (IsDown (n + 5)) (IsDown (n + 6)) (IsDown (n + 7)) (IsDown (n + 8))
    (Int.fract_nonneg _) hDn.delta_lt hD9.delta_lt
    (by have := delta_add n 1 1 (by norm_num; linarith) (by norm_num; linarith); push_cast at this; exact this)
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    (by have := delta_add n 2 3 (by norm_num; linarith) (by norm_num; linarith); push_cast at this; exact this)
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    (by have := delta_add n 3 4 (by norm_num; linarith) (by norm_num; linarith); push_cast at this; exact this)
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    (by have := delta_add n 4 6 (by norm_num; linarith) (by norm_num; linarith); push_cast at this; exact this)
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    (by have := delta_add n 5 8 (by norm_num; linarith) (by norm_num; linarith); push_cast at this; exact this)
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    (by have := delta_add n 6 9 (by norm_num; linarith) (by norm_num; linarith); push_cast at this; exact this)
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    (by have := delta_add n 7 11 (by norm_num; linarith) (by norm_num; linarith); push_cast at this; exact this)
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    (by have := delta_add n 8 12 (by norm_num; linarith) (by norm_num; linarith); push_cast at this; exact this)
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    (by have := delta_add n 9 14 (by norm_num; linarith) (by norm_num; linarith); push_cast at this; exact this)
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    (fun h => h.delta_lt) (U 1) (fun h => h.delta_lt) (U 2) (fun h => h.delta_lt) (U 3)
    (fun h => h.delta_lt) (U 4) (fun h => h.delta_lt) (U 5) (fun h => h.delta_lt) (U 6)
    (fun h => h.delta_lt) (U 7) (fun h => h.delta_lt) (U 8)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | exact P1 0 hDn'
    | exact P3 0 hDn'
    | exact P8 0 hDn'
    | exact fun h => M2 9 (by norm_num) hD9' h
    | exact fun h => M5 9 (by norm_num) hD9' h
    | exact P1 _
    | exact M2 _ (by norm_num)
    | exact P3 _
    | exact M5 _ (by norm_num)
    | exact P8 _
    | simpa [Nat.count_succ, add_assoc] using hc

/-- **`9 ∈ U₄`**: `8, 11, 14, 16, 17` are consecutive up-integers. -/
theorem nine_mem_up : 9 ∈ gapSet IsUp 4 := by
  obtain ⟨h8, h17, c8, c17⟩ := up_facts
  refine ⟨3, ?_⟩
  have e8 : nth IsUp 3 = 8 := by rw [← c8]; exact Nat.nth_count h8
  have e17 : nth IsUp (3 + 4) = 17 := by rw [show 3 + 4 = 7 from rfl, ← c17]; exact Nat.nth_count h17
  rw [e8, e17]

/-- **Aliabadi's theorem**: `9 ∈ U₄ \ D₄`. -/
theorem nine_mem_up_not_down : 9 ∈ gapSet IsUp 4 ∧ 9 ∉ gapSet IsDown 4 :=
  ⟨nine_mem_up, nine_not_mem_down⟩

/-- **The Chung–Graham–Spiro gap-set conjecture is false**: `D_ℓ = U_ℓ` fails for `ℓ = 4`. -/
theorem not_gapSet_conjecture : ¬ ∀ ℓ, 1 ≤ ℓ → gapSet IsDown ℓ = gapSet IsUp ℓ := fun h =>
  nine_not_mem_down ((h 4 (by norm_num)).symm ▸ nine_mem_up)

end OpenProblemsLab.FibWalk
