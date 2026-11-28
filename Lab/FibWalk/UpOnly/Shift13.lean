import Lab.FibWalk.Seven.Main

/-!
# The shift `-13` for down-integers

Down-integers `≥ 105` have representation parameter `t ≥ 8` (`eight_le_of_rep`), so the general shift
lemma `shift` applies with `j = 7`: a down-integer `N ≥ 105` with `δ N ≥ θ₇` has `N - 13` down as well.
Used by the generated `UpOnly/L*Patterns.lean` files (`explorer/fib-walk/gen_up_only.py`).
-/

namespace OpenProblemsLab.FibWalk

open Real
open scoped goldenRatio

/-- `θ₇ = (17φ - 26)/5`, for the shift `-13`. -/
noncomputable def θ₇ : ℝ := (17 * φ - 26) / 5

lemma hθ₇ : θ₇ * √5 * φ ^ (7 - 1) = φ ^ (7 - 2) + 1 := by
  show θ₇ * √5 * φ ^ 6 = φ ^ 5 + 1
  rw [θ₇, sqrt5_eq]
  linear_combination (34 / 5 * φ ^ 6 - 7 * φ ^ 5 + 5 * φ ^ 4 - 3 * φ ^ 3 + 2 * φ ^ 2 - φ + 1) * goldenRatio_sq

lemma shift_minus13 {N : ℕ} (hN : 105 ≤ N) (h : IsDown N) (hδ : θ₇ ≤ δ N) : IsDown (N - 13) := by
  obtain ⟨n', hn', hd⟩ := shift' θ₇ (by norm_num) (by norm_num) hθ₇ hN h hδ
  have : n' = N - 13 := by norm_num [Nat.fib] at hn'; omega
  rwa [this] at hd

/-! Shift facts in the form the generated window lemmas use: if `n + p` is down and `n + q` is not,
where `n + q` is the shift of `n + p`, then `δ (n + p)` is below the shift threshold. -/

lemma sf_plus1 {n p q : ℕ} (hpq : n + p + 1 = n + q) (hn : 105 ≤ n + p) (hP : IsDown (n + p))
    (hQ : ¬ IsDown (n + q)) : δ (n + p) < θ₂ :=
  lt_of_not_ge fun h => hQ (hpq ▸ shift_plus1 hn hP h)

lemma sf_minus2 {n p q : ℕ} (hpq : n + p - 2 = n + q) (hn : 105 ≤ n + p) (hP : IsDown (n + p))
    (hQ : ¬ IsDown (n + q)) : δ (n + p) < θ₃ :=
  lt_of_not_ge fun h => hQ (hpq ▸ shift_minus2 hn hP h)

lemma sf_plus3 {n p q : ℕ} (hpq : n + p + 3 = n + q) (hn : 105 ≤ n + p) (hP : IsDown (n + p))
    (hQ : ¬ IsDown (n + q)) : δ (n + p) < θ₄ :=
  lt_of_not_ge fun h => hQ (hpq ▸ shift_plus3 hn hP h)

lemma sf_minus5 {n p q : ℕ} (hpq : n + p - 5 = n + q) (hn : 105 ≤ n + p) (hP : IsDown (n + p))
    (hQ : ¬ IsDown (n + q)) : δ (n + p) < θ₅ :=
  lt_of_not_ge fun h => hQ (hpq ▸ shift_minus5 hn hP h)

lemma sf_plus8 {n p q : ℕ} (hpq : n + p + 8 = n + q) (hn : 105 ≤ n + p) (hP : IsDown (n + p))
    (hQ : ¬ IsDown (n + q)) : δ (n + p) < θ₆ :=
  lt_of_not_ge fun h => hQ (hpq ▸ shift_plus8 hn hP h)

lemma sf_minus13 {n p q : ℕ} (hpq : n + p - 13 = n + q) (hn : 105 ≤ n + p) (hP : IsDown (n + p))
    (hQ : ¬ IsDown (n + q)) : δ (n + p) < θ₇ :=
  lt_of_not_ge fun h => hQ (hpq ▸ shift_minus13 hn hP h)

end OpenProblemsLab.FibWalk
